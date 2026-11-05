#!/usr/bin/env python3
"""
WiFi Analyzer
=============

Mostra tutte le reti Wi-Fi visibili sulle bande 2.4 GHz, 5 GHz e 6 GHz.
Ogni rete e' disegnata come una "campana" centrata sul proprio canale, larga
quanto la sua banda (20/40/80/160/320 MHz) e alta quanto il segnale (dBm):
dove le campane si sovrappongono i canali interferiscono.

Per ogni rete viene calcolata anche la velocita' PHY massima teorica offerta
dall'access point (generazione Wi-Fi, numero di stream spaziali, MCS massimo e
larghezza di canale in uso).

Sorgenti dati:
  * Windows : WLAN API native (wlanapi.dll) -> RSSI, frequenza, larghezza di
              canale e capacita' ricavate dagli Information Element 802.11.
  * Linux   : nmcli (NetworkManager).
  * --demo  : reti simulate, utile per provare l'interfaccia.

Ogni scansione puo' essere salvata come CSV (wifi_scan_AAAA-MM-GG_hh-mm-ss.csv)
e una cartella di salvataggi puo' essere riprodotta in modalita' playback.

Notifiche su Microsoft Teams (menu Notifiche): riepilogo periodico ogni N ore e
avviso quando un canale ha piu' di X reti sovrapposte, con il grafico allegato.
Serve l'URL di un webhook creato in Teams con l'app Workflows ("Post to a channel
when a webhook request is received"); in alternativa alla finestra impostazioni
si puo' passare con la variabile d'ambiente WIFI_ANALYZER_TEAMS_WEBHOOK.

Uso:
  python wifi_analyzer.py                      # scansione live
  python wifi_analyzer.py --demo               # dati simulati
  python wifi_analyzer.py --save-dir logs      # live + salvataggio CSV in logs/
  python wifi_analyzer.py --playback logs      # riproduce i CSV salvati in logs/
  python wifi_analyzer.py --snapshot x.png     # una scansione, salva PNG + tabella su console

Requisiti: Python 3.8+, matplotlib (pip install matplotlib).
Nota Windows 11: la scansione Wi-Fi richiede che "Posizione" sia attiva e che
le app desktop possano accedervi (Impostazioni > Privacy e sicurezza > Posizione).
"""

import argparse
import base64
import csv
import ctypes
import dataclasses
import io
import itertools
import json
import os
import queue
import random
import re
import socket
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.request
import zlib
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path

import numpy as np
from matplotlib.figure import Figure

FLOOR_DBM = -100
TOP_DBM = -10

# --------------------------------------------------------------------------
# Bande e canali
# --------------------------------------------------------------------------

BANDS = {
    "2.4": dict(title="2.4 GHz", fmin=2400, fmax=2495,
                channels=list(range(1, 15)), labels=list(range(1, 15))),
    "5": dict(title="5 GHz", fmin=5150, fmax=5895,
              channels=list(range(36, 178, 4)), labels=list(range(36, 178, 4))),
    "6": dict(title="6 GHz", fmin=5925, fmax=7125,
              channels=list(range(1, 234, 4)), labels=list(range(1, 234, 8))),
}

# Sottobande DFS a 5 GHz (radar detection): evidenziate nel grafico
DFS_RANGES = [(5250, 5350), (5470, 5730)]


def band_of(freq):
    if 2400 <= freq < 2500:
        return "2.4"
    if 5150 <= freq < 5925:
        return "5"
    if 5925 <= freq <= 7125:
        return "6"
    return None


def freq_to_channel(freq):
    band = band_of(freq)
    if band == "2.4":
        return 14 if freq == 2484 else (freq - 2407) // 5
    if band == "5":
        return (freq - 5000) // 5
    if band == "6":
        return 2 if freq == 5935 else (freq - 5950) // 5
    return 0


def channel_to_freq(ch, band):
    if band == "2.4":
        return 2484 if ch == 14 else 2407 + 5 * ch
    if band == "5":
        return 5000 + 5 * ch
    if band == "6":
        return 5935 if ch == 2 else 5950 + 5 * ch
    raise ValueError(band)


def estimate_center(freq, width):
    """Centro del canale largo quando si conosce solo il canale primario.

    A 5/6 GHz i blocchi da 40/80/160/320 MHz sono allineati a una griglia fissa;
    a 2.4 GHz si assume il canale secondario sopra per ch<=7, sotto altrimenti.
    """
    band = band_of(freq)
    if width <= 20 or band is None:
        return freq
    ch = freq_to_channel(freq)
    if band == "2.4":
        return freq + 10 if ch <= 7 else freq - 10
    n = width // 5  # larghezza espressa in "unita' di numero di canale"
    first = 1 if band == "6" else (149 if ch >= 149 else 36)
    start = first + ((ch - first) // n) * n
    return channel_to_freq(start + (n - 4) // 2, band)


# --------------------------------------------------------------------------
# Velocita' PHY teorica
# --------------------------------------------------------------------------

# Sottoportanti dati per larghezza di canale
_NSD_HT = {20: 52, 40: 108, 80: 234, 160: 468}                 # 802.11n / ac
_NSD_HE = {20: 234, 40: 468, 80: 980, 160: 1960, 320: 3920}   # 802.11ax / be
# bit per sottoportante x code rate, per MCS 0..13
_MCS_BITS = [0.5, 1, 1.5, 2, 3, 4, 4.5, 5, 6, 20 / 3, 7.5, 25 / 3, 9, 10]


def phy_rate(kind, width, nss, mcs, short_gi=False):
    """Velocita' PHY in Mbps. kind: HT, VHT, HE, EHT."""
    if kind in ("HE", "EHT"):
        nsd, t_sym = _NSD_HE.get(width, 0), 13.6        # 12.8 us + GI 0.8 us
    else:
        nsd, t_sym = _NSD_HT.get(width, 0), (3.6 if short_gi else 4.0)
    return nsd * _MCS_BITS[mcs] * nss / t_sym


def gen_name(kind, band):
    return {"EHT": "Wi-Fi 7 (be)",
            "HE": "Wi-Fi 6E (ax)" if band == "6" else "Wi-Fi 6 (ax)",
            "VHT": "Wi-Fi 5 (ac)",
            "HT": "Wi-Fi 4 (n)"}[kind]


# --------------------------------------------------------------------------
# Modello dati
# --------------------------------------------------------------------------

@dataclass
class Network:
    ssid: str
    bssid: str
    rssi: int            # dBm
    primary_freq: int    # MHz, canale primario
    width: int = 20      # MHz
    center_freq: int = 0  # MHz, centro dell'intero canale (puo' differire dal primario)
    standard: str = ""
    max_rate: float = 0.0  # Mbps, velocita' PHY massima teorica
    nss: int = 0           # stream spaziali
    mcs: int = -1          # MCS massimo
    util: float = -1.0     # % di tempo canale occupato dichiarato dall'AP (BSS Load), -1 = n/d
    stations: int = -1     # client associati dichiarati dall'AP (BSS Load), -1 = n/d
    overlaps: list = field(default_factory=list)  # [(Network, tipo, MHz sovrapposti)]

    def __post_init__(self):
        if not self.center_freq:
            self.center_freq = self.primary_freq

    @property
    def band(self):
        return band_of(self.primary_freq)

    @property
    def channel(self):
        return freq_to_channel(self.primary_freq)

    @property
    def low(self):
        return self.center_freq - self.width / 2

    @property
    def high(self):
        return self.center_freq + self.width / 2

    @property
    def name(self):
        return self.ssid if self.ssid else "<nascosta>"

    @property
    def rate_text(self):
        return f"{self.max_rate:.0f} Mbps" if self.max_rate else ""

    @property
    def stream_text(self):
        if not self.nss:
            return ""
        return f"{self.nss}x{self.nss}" + (f" MCS{self.mcs}" if self.mcs >= 0 else "")

    @property
    def util_text(self):
        return f"{self.util:.0f} %" if self.util >= 0 else ""

    @property
    def stations_text(self):
        return str(self.stations) if self.stations >= 0 else ""


def radio_key(n):
    """Identifica la radio fisica: un AP con piu' SSID usa BSSID che differiscono
    solo nell'ultimo byte (e a volte nel bit "locally administered" del primo)."""
    return (":".join(n.bssid.split(":")[1:5]), n.primary_freq, n.width)


def group_radios(nets):
    """Unisce gli SSID virtuali trasmessi dalla stessa radio (es. IIT / eduroam / Guest)."""
    groups = {}
    for n in sorted(nets, key=lambda n: -n.rssi):
        groups.setdefault(radio_key(n), []).append(n)
    radios = []
    for members in groups.values():
        names = list(dict.fromkeys(m.name for m in members))
        fastest = max(members, key=lambda m: m.max_rate)
        stations = [m.stations for m in members if m.stations >= 0]
        radios.append(dataclasses.replace(members[0], ssid=" / ".join(names), overlaps=[],
                                          standard=fastest.standard, max_rate=fastest.max_rate,
                                          nss=fastest.nss, mcs=fastest.mcs,
                                          util=max(m.util for m in members),
                                          stations=sum(stations) if stations else -1))
    return radios


def compute_overlaps(nets, min_rssi):
    """Per ogni rete calcola con quali altre (stessa banda, sopra soglia, radio diversa)
    si sovrappone."""
    for n in nets:
        n.overlaps = []
    visible = [n for n in nets if n.rssi >= min_rssi]
    for a, b in itertools.combinations(visible, 2):
        if a.band != b.band or radio_key(a) == radio_key(b):
            continue
        mhz = min(a.high, b.high) - max(a.low, b.low)
        if mhz <= 0:
            continue
        kind = "stesso canale" if a.primary_freq == b.primary_freq else "parziale"
        a.overlaps.append((b, kind, mhz))
        b.overlaps.append((a, kind, mhz))


def congestion_segments(nets):
    """Intervalli di frequenza coperti da 2 o piu' radio: [(f_lo, f_hi, n_radio)]."""
    edges = sorted({n.low for n in nets} | {n.high for n in nets})
    segs = []
    for lo, hi in zip(edges, edges[1:]):
        mid = (lo + hi) / 2
        count = len({radio_key(n) for n in nets if n.low < mid < n.high})
        if count >= 2:
            if segs and segs[-1][1] == lo and segs[-1][2] == count:
                segs[-1] = (segs[-1][0], hi, count)
            else:
                segs.append((lo, hi, count))
    return segs


def channel_utilization(nets):
    """Utilizzo per canale primario: {freq primario: % massima dichiarata dagli AP}.

    Il campo BSS Load riporta la frazione di tempo in cui l'AP ha sentito il proprio
    canale primario occupato da qualunque trasmissione (anche di altre reti).
    """
    util = {}
    for n in nets:
        if n.util >= 0:
            util[n.primary_freq] = max(util.get(n.primary_freq, 0.0), n.util)
    return util


def util_color(u):
    if u < 30:
        return "#2ca02c"
    if u < 50:
        return "#e6c229"
    if u < 70:
        return "#ff7f0e"
    return "#d62728"


def overlap_summary(n):
    return "; ".join(f"{o.name} (ch {o.channel}, {kind}, {mhz:.0f} MHz)"
                     for o, kind, mhz in sorted(n.overlaps, key=lambda t: -t[0].rssi))


# --------------------------------------------------------------------------
# Parsing degli Information Element 802.11
# --------------------------------------------------------------------------

def iter_ies(ies):
    """Genera (element_id, dati). Per l'ID 255 (extension) i dati iniziano con l'ext ID."""
    i = 0
    while i + 2 <= len(ies):
        eid, ln = ies[i], ies[i + 1]
        data = ies[i + 2:i + 2 + ln]
        if len(data) < ln:
            return
        yield eid, data
        i += 2 + ln


def parse_channel_width(ies, primary_freq):
    """Restituisce (larghezza MHz, frequenza centrale MHz) leggendo HT/VHT/HE/EHT Operation."""
    band = band_of(primary_freq)
    width, center = 20, primary_freq
    if band is None:
        return width, center

    def ch2f(ch):
        return channel_to_freq(ch, band)

    ht = vht = he = eht = None
    for eid, data in iter_ies(ies):
        if eid == 61 and len(data) >= 2:          # HT Operation
            ht = data
        elif eid == 192 and len(data) >= 3:       # VHT Operation
            vht = data
        elif eid == 255 and data:
            if data[0] == 36:                     # HE Operation
                he = data[1:]
            elif data[0] == 106:                  # EHT Operation
                eht = data[1:]

    if ht is not None:
        offset = ht[1] & 0x03
        if (ht[1] & 0x04) and offset in (1, 3):
            width = 40
            center = primary_freq + (10 if offset == 1 else -10)

    if vht is not None and band != "2.4":
        w, c0, c1 = vht[0], vht[1], vht[2]
        if w == 1 and c0:
            if c1 and abs(c1 - c0) == 8:
                width, center = 160, ch2f(c1)
            else:  # 80 MHz (o 80+80: si mostra il segmento primario)
                width, center = 80, ch2f(c0)
        elif w == 2 and c0:  # codifica 160 MHz deprecata
            width, center = 160, ch2f(c0)
        elif w == 3 and c0:  # 80+80 deprecato
            width, center = 80, ch2f(c0)

    if he is not None and len(he) >= 6:
        params = he[0] | (he[1] << 8) | (he[2] << 16)
        pos = 6  # HE Operation Parameters(3) + BSS Color(1) + Basic HE-MCS(2)
        if params & (1 << 14):
            pos += 3  # VHT Operation Information
        if params & (1 << 15):
            pos += 1  # Max Co-Hosted BSSID Indicator
        if (params & (1 << 17)) and len(he) >= pos + 5:  # 6 GHz Operation Information
            ctrl, c0, c1 = he[pos + 1], he[pos + 2], he[pos + 3]
            w = ctrl & 0x03
            if w == 0:
                width, center = 20, primary_freq
            elif w == 1 and c0:
                width, center = 40, ch2f(c0)
            elif w == 2 and c0:
                width, center = 80, ch2f(c0)
            elif w == 3 and c0:
                if c1 and abs(c1 - c0) == 8:
                    width, center = 160, ch2f(c1)
                else:
                    width, center = 80, ch2f(c0)

    if eht is not None and len(eht) >= 8 and (eht[0] & 0x01):
        ctrl, c1 = eht[5], eht[7]
        if (ctrl & 0x07) == 4 and c1:  # 320 MHz
            width, center = 320, ch2f(c1)

    # Difesa contro IE incoerenti: il primario deve stare dentro il canale
    if abs(center - primary_freq) >= width / 2:
        width, center = 20, primary_freq
    return width, center


def parse_bss_load(ies):
    """BSS Load (ID 11): (utilizzo canale %, stazioni associate), oppure (-1, -1)."""
    for eid, data in iter_ies(ies):
        if eid == 11 and len(data) >= 5:
            return data[2] * 100 / 255, data[0] | (data[1] << 8)
    return -1.0, -1


def _mcs_map(value, table):
    """Decodifica una mappa MCS/NSS a 2 bit per stream: (nss, mcs massimo)."""
    nss, mcs = 0, -1
    for ss in range(8):
        v = (value >> (2 * ss)) & 0x03
        if v != 3:
            nss, mcs = ss + 1, table[v]
    return nss, mcs


def _ht_short_gi(ht, width):
    if ht is None:
        return False
    info = ht[0] | (ht[1] << 8)
    return bool(info & (1 << 5)) if width <= 20 else bool(info & (1 << 6))


def parse_capabilities(ies, band, width):
    """Velocita' massima offerta dall'AP: (generazione, Mbps, nss, mcs).

    Usa le Capabilities HT/VHT/HE/EHT (stream spaziali e MCS massimo supportati
    in ricezione dall'AP) combinate con la larghezza di canale in uso.
    """
    ht = vht = he = eht = None
    legacy = 0.0
    for eid, data in iter_ies(ies):
        if eid in (1, 50):  # Supported / Extended Supported Rates (unita' da 500 kbps)
            rates = [(b & 0x7F) * 0.5 for b in data if (b & 0x7F) <= 108]
            legacy = max([legacy] + rates)
        elif eid == 45 and len(data) >= 7:        # HT Capabilities
            ht = data
        elif eid == 191 and len(data) >= 6:       # VHT Capabilities
            vht = data
        elif eid == 255 and data:
            if data[0] == 35:                     # HE Capabilities
                he = data[1:]
            elif data[0] == 108:                  # EHT Capabilities
                eht = data[1:]

    best = None  # (tipo, nss, mcs, short_gi)
    if eht is not None and len(eht) >= 14:
        # EHT-MCS map <=80 MHz: un byte per gruppo MCS 0-9 / 10-11 / 12-13, nibble basso = Rx NSS
        b0, b1, b2 = eht[11] & 0x0F, eht[12] & 0x0F, eht[13] & 0x0F
        if b2:
            best = ("EHT", b2, 13, False)
        elif b1:
            best = ("EHT", b1, 11, False)
        elif b0:
            best = ("EHT", b0, 9, False)
    if best is None and he is not None and len(he) >= 19:
        # HE MAC(6) + HE PHY(11), poi Rx HE-MCS map <=80 MHz
        nss, mcs = _mcs_map(he[17] | (he[18] << 8), {0: 7, 1: 9, 2: 11})
        if nss:
            best = ("HE", nss, mcs, False)
    if best is None and vht is not None and band != "2.4":
        info = int.from_bytes(bytes(vht[0:4]), "little")
        nss, mcs = _mcs_map(vht[4] | (vht[5] << 8), {0: 7, 1: 8, 2: 9})
        if nss:
            if width == 20:
                mcs = min(mcs, 8)  # MCS9 non valido a 20 MHz
            if width == 80:
                sgi = bool(info & (1 << 5))
            elif width >= 160:
                sgi = bool(info & (1 << 6))
            else:
                sgi = _ht_short_gi(ht, width)
            best = ("VHT", nss, mcs, sgi)
    if best is None and ht is not None:
        nss = min(sum(1 for b in ht[3:7] if b), 4)
        if nss:
            best = ("HT", nss, 7, _ht_short_gi(ht, min(width, 40)))

    if best is None:
        if not legacy:
            return "", 0.0, 0, -1
        return ("802.11b" if legacy <= 11 else "802.11a/g"), legacy, 1, -1

    kind, nss, mcs, sgi = best
    w = width
    if kind == "HT":
        w = min(width, 40)
    elif kind in ("VHT", "HE"):
        w = min(width, 160)
    return gen_name(kind, band), phy_rate(kind, w, nss, mcs, sgi), nss, mcs


# --------------------------------------------------------------------------
# Scanner: Windows (WLAN API)
# --------------------------------------------------------------------------

class _GUID(ctypes.Structure):
    _fields_ = [("Data1", ctypes.c_uint32), ("Data2", ctypes.c_uint16),
                ("Data3", ctypes.c_uint16), ("Data4", ctypes.c_ubyte * 8)]


class _WLAN_INTERFACE_INFO(ctypes.Structure):
    _fields_ = [("InterfaceGuid", _GUID),
                ("strInterfaceDescription", ctypes.c_wchar * 256),
                ("isState", ctypes.c_int)]


class _WLAN_INTERFACE_INFO_LIST(ctypes.Structure):
    _fields_ = [("dwNumberOfItems", ctypes.c_uint32), ("dwIndex", ctypes.c_uint32),
                ("InterfaceInfo", _WLAN_INTERFACE_INFO * 1)]


class _DOT11_SSID(ctypes.Structure):
    _fields_ = [("uSSIDLength", ctypes.c_uint32), ("ucSSID", ctypes.c_ubyte * 32)]


class _WLAN_RATE_SET(ctypes.Structure):
    _fields_ = [("uRateSetLength", ctypes.c_uint32), ("usRateSet", ctypes.c_uint16 * 126)]


class _WLAN_BSS_ENTRY(ctypes.Structure):
    _fields_ = [("dot11Ssid", _DOT11_SSID),
                ("uPhyId", ctypes.c_uint32),
                ("dot11Bssid", ctypes.c_ubyte * 6),
                ("dot11BssType", ctypes.c_int),
                ("dot11BssPhyType", ctypes.c_int),
                ("lRssi", ctypes.c_int32),
                ("uLinkQuality", ctypes.c_uint32),
                ("bInRegDomain", ctypes.c_ubyte),
                ("usBeaconPeriod", ctypes.c_uint16),
                ("ullTimestamp", ctypes.c_uint64),
                ("ullHostTimestamp", ctypes.c_uint64),
                ("usCapabilityInformation", ctypes.c_uint16),
                ("ulChCenterFrequency", ctypes.c_uint32),  # kHz
                ("wlanRateSet", _WLAN_RATE_SET),
                ("ulIeOffset", ctypes.c_uint32),
                ("ulIeSize", ctypes.c_uint32)]


class _WLAN_BSS_LIST(ctypes.Structure):
    _fields_ = [("dwTotalSize", ctypes.c_uint32), ("dwNumberOfItems", ctypes.c_uint32),
                ("wlanBssEntries", _WLAN_BSS_ENTRY * 1)]


_PHY_NAMES = {1: "FHSS", 2: "802.11", 4: "802.11a", 5: "802.11b", 6: "802.11g",
              7: "802.11n", 8: "802.11ac", 9: "802.11ad", 10: "802.11ax", 11: "802.11be"}

ERROR_ACCESS_DENIED = 5


class WindowsScanner:
    name = "Windows WLAN API"
    SCAN_WAIT_S = 4.0  # Windows completa una scansione entro 4 secondi

    def __init__(self):
        api = ctypes.WinDLL("wlanapi.dll")
        P = ctypes.POINTER
        api.WlanOpenHandle.argtypes = [ctypes.c_uint32, ctypes.c_void_p,
                                       P(ctypes.c_uint32), P(ctypes.c_void_p)]
        api.WlanOpenHandle.restype = ctypes.c_uint32
        api.WlanCloseHandle.argtypes = [ctypes.c_void_p, ctypes.c_void_p]
        api.WlanCloseHandle.restype = ctypes.c_uint32
        api.WlanEnumInterfaces.argtypes = [ctypes.c_void_p, ctypes.c_void_p,
                                           P(P(_WLAN_INTERFACE_INFO_LIST))]
        api.WlanEnumInterfaces.restype = ctypes.c_uint32
        api.WlanScan.argtypes = [ctypes.c_void_p, P(_GUID), ctypes.c_void_p,
                                 ctypes.c_void_p, ctypes.c_void_p]
        api.WlanScan.restype = ctypes.c_uint32
        api.WlanGetNetworkBssList.argtypes = [ctypes.c_void_p, P(_GUID), ctypes.c_void_p,
                                              ctypes.c_int, ctypes.c_int, ctypes.c_void_p,
                                              P(P(_WLAN_BSS_LIST))]
        api.WlanGetNetworkBssList.restype = ctypes.c_uint32
        api.WlanFreeMemory.argtypes = [ctypes.c_void_p]
        api.WlanFreeMemory.restype = None
        self.api = api

        self.handle = ctypes.c_void_p()
        negotiated = ctypes.c_uint32()
        err = api.WlanOpenHandle(2, None, ctypes.byref(negotiated), ctypes.byref(self.handle))
        if err:
            raise OSError(err, f"WlanOpenHandle fallita (errore {err}). Il servizio WLAN AutoConfig e' attivo?")
        if not self._interfaces():
            raise RuntimeError("Nessuna scheda Wi-Fi trovata.")

    def close(self):
        if self.handle:
            self.api.WlanCloseHandle(self.handle, None)
            self.handle = ctypes.c_void_p()

    def _interfaces(self):
        plist = ctypes.POINTER(_WLAN_INTERFACE_INFO_LIST)()
        err = self.api.WlanEnumInterfaces(self.handle, None, ctypes.byref(plist))
        if err:
            raise OSError(err, f"WlanEnumInterfaces fallita (errore {err})")
        try:
            count = plist.contents.dwNumberOfItems
            arr = ctypes.cast(ctypes.addressof(plist.contents.InterfaceInfo),
                              ctypes.POINTER(_WLAN_INTERFACE_INFO))
            return [_GUID.from_buffer_copy(arr[i].InterfaceGuid) for i in range(count)]
        finally:
            self.api.WlanFreeMemory(ctypes.cast(plist, ctypes.c_void_p))

    def scan(self):
        guids = self._interfaces()
        for g in guids:
            self.api.WlanScan(self.handle, ctypes.byref(g), None, None, None)
        time.sleep(self.SCAN_WAIT_S)

        found = {}
        for g in guids:
            plist = ctypes.POINTER(_WLAN_BSS_LIST)()
            err = self.api.WlanGetNetworkBssList(self.handle, ctypes.byref(g), None,
                                                 3, 0, None, ctypes.byref(plist))
            if err == ERROR_ACCESS_DENIED:
                raise PermissionError(
                    "Accesso alla scansione Wi-Fi negato.\n"
                    "Su Windows 11 attiva Impostazioni > Privacy e sicurezza > Posizione\n"
                    "e \"Consenti alle app desktop di accedere alla posizione\".")
            if err:
                continue
            try:
                lst = plist.contents
                arr = ctypes.cast(ctypes.addressof(lst.wlanBssEntries),
                                  ctypes.POINTER(_WLAN_BSS_ENTRY))
                for i in range(lst.dwNumberOfItems):
                    e = arr[i]
                    freq = int(round(e.ulChCenterFrequency / 1000))
                    band = band_of(freq)
                    if band is None:
                        continue
                    ssid_len = min(e.dot11Ssid.uSSIDLength, 32)
                    ssid = bytes(e.dot11Ssid.ucSSID[:ssid_len]).decode("utf-8", "replace")
                    ssid = ssid.strip("\x00")
                    bssid = ":".join(f"{b:02x}" for b in e.dot11Bssid)
                    ies = ctypes.string_at(ctypes.addressof(e) + e.ulIeOffset, e.ulIeSize)
                    width, center = parse_channel_width(ies, freq)
                    gen, rate, nss, mcs = parse_capabilities(ies, band, width)
                    util, stations = parse_bss_load(ies)
                    found[bssid] = Network(ssid, bssid, int(e.lRssi), freq, width, center,
                                           gen or _PHY_NAMES.get(e.dot11BssPhyType, ""),
                                           rate, nss, mcs, util, stations)
            finally:
                self.api.WlanFreeMemory(ctypes.cast(plist, ctypes.c_void_p))
        return list(found.values())


# --------------------------------------------------------------------------
# Scanner: Linux (nmcli)
# --------------------------------------------------------------------------

class NmcliScanner:
    name = "nmcli"
    FIELD_SETS = ("SSID,BSSID,FREQ,SIGNAL,BANDWIDTH,RATE", "SSID,BSSID,FREQ,SIGNAL,RATE",
                  "SSID,BSSID,FREQ,SIGNAL")

    def __init__(self):
        subprocess.run(["nmcli", "--version"], capture_output=True, check=True)

    @staticmethod
    def _split(line):
        # in modalita' terse i ':' dentro i campi sono escapati con '\'
        return [f.replace("\\:", ":") for f in re.split(r"(?<!\\):", line)]

    @staticmethod
    def _num(text):
        digits = re.sub(r"[^\d.]", "", text or "")
        return float(digits) if digits else 0.0

    def scan(self):
        for fields in self.FIELD_SETS:
            res = subprocess.run(["nmcli", "-t", "-f", fields, "dev", "wifi", "list",
                                  "--rescan", "yes"], capture_output=True, text=True)
            if res.returncode == 0:
                break
        else:
            raise RuntimeError(res.stderr.strip() or "nmcli fallito")

        names = fields.split(",")
        nets = {}
        for line in res.stdout.splitlines():
            row = dict(zip(names, self._split(line)))
            if len(row) < len(names):
                continue
            freq = int(self._num(row["FREQ"]))
            if band_of(freq) is None:
                continue
            width = int(self._num(row.get("BANDWIDTH"))) or 20
            rssi = int(self._num(row["SIGNAL"])) // 2 - 100  # qualita' % -> dBm approssimati
            bssid = row["BSSID"].lower()
            nets[bssid] = Network(row["SSID"], bssid, rssi, freq, width,
                                  estimate_center(freq, width),
                                  max_rate=self._num(row.get("RATE")))
        return list(nets.values())


# --------------------------------------------------------------------------
# Scanner: dati simulati
# --------------------------------------------------------------------------

class DemoScanner:
    name = "Demo (dati simulati)"
    BASE = [
        # ssid,           banda, canale, larghezza, dBm, tipo, stream
        ("Casa",          "2.4", 1, 20, -42, "HE", 2),
        ("Vicino_1",      "2.4", 3, 20, -71, "HT", 2),
        ("FASTWEB-A1B2",  "2.4", 6, 20, -58, "HT", 3),
        ("TIM-12345678",  "2.4", 6, 40, -74, "HT", 2),
        ("Ospiti",        "2.4", 11, 20, -55, "HE", 2),
        ("iCub-lab",      "2.4", 11, 20, -79, "HT", 1),
        ("",              "2.4", 9, 20, -86, "HT", 1),
        ("Casa_5G",       "5", 36, 80, -48, "HE", 2),
        ("Vicino_5G",     "5", 44, 40, -70, "VHT", 2),
        ("Ufficio",       "5", 100, 160, -63, "HE", 4),
        ("Lab",           "5", 149, 80, -57, "VHT", 3),
        ("Stampante",     "5", 157, 20, -81, "HT", 1),
        ("Casa_6G",       "6", 37, 160, -60, "HE", 2),
        ("Neighbor_6E",   "6", 53, 80, -77, "HE", 2),
        ("WiFi7-AP",      "6", 69, 320, -69, "EHT", 2),
    ]
    MAX_MCS = {"HT": 7, "VHT": 9, "HE": 11, "EHT": 13}

    def __init__(self):
        self.rng = random.Random()
        r = random.Random(1234)
        self.bssids = [":".join(f"{r.randrange(256):02x}" for _ in range(6)) for _ in self.BASE]

    def scan(self):
        time.sleep(0.4)
        nets = []
        for (ssid, band, ch, width, rssi, kind, nss), bssid in zip(self.BASE, self.bssids):
            f = channel_to_freq(ch, band)
            mcs = 8 if (kind == "VHT" and width == 20) else self.MAX_MCS[kind]
            w = min(width, 40) if kind == "HT" else width
            # meta' degli AP simulati dichiara il BSS Load, con carico variabile nel tempo
            has_load = zlib.crc32(bssid.encode()) % 2 == 0
            util = min(100.0, max(0.0, (35 if band == "2.4" else 15) + self.rng.gauss(0, 15)))
            nets.append(Network(ssid, bssid, rssi + self.rng.randint(-3, 3), f, width,
                                estimate_center(f, width), gen_name(kind, band),
                                phy_rate(kind, w, nss, mcs, short_gi=True), nss, mcs,
                                util if has_load else -1.0,
                                self.rng.randint(0, 12) if has_load else -1))
        return nets


def make_scanner(demo):
    if demo:
        return DemoScanner()
    if sys.platform == "win32":
        return WindowsScanner()
    if sys.platform.startswith("linux"):
        return NmcliScanner()
    raise RuntimeError(f"Piattaforma {sys.platform} non supportata: usa --demo")


# --------------------------------------------------------------------------
# Salvataggio / caricamento CSV
# --------------------------------------------------------------------------

CSV_PREFIX = "wifi_scan_"
CSV_FIELDS = ["Data/ora", "SSID", "BSSID", "Banda", "Canale", "Frequenza MHz", "Larghezza MHz",
              "Centro MHz", "Segnale dBm", "Standard", "Max PHY Mbps", "Stream", "MCS max",
              "Utilizzo canale %", "Stazioni", "N sovrapposizioni", "Sovrapposta con"]


def write_csv(f, nets, when, min_rssi):
    """Scrive la tabella (una riga per BSSID) sul file di testo f."""
    compute_overlaps(nets, min_rssi)
    w = csv.writer(f)
    w.writerow(CSV_FIELDS)
    stamp = when.strftime("%Y-%m-%d %H:%M:%S")
    for n in sorted(nets, key=lambda n: (n.primary_freq, -n.rssi)):
        w.writerow([stamp, n.ssid, n.bssid, BANDS[n.band]["title"], n.channel,
                    n.primary_freq, n.width, n.center_freq, n.rssi, n.standard,
                    f"{n.max_rate:.1f}" if n.max_rate else "", n.nss or "",
                    n.mcs if n.mcs >= 0 else "", f"{n.util:.1f}" if n.util >= 0 else "",
                    n.stations_text, len(n.overlaps), overlap_summary(n)])


def csv_filename(when):
    return f"{CSV_PREFIX}{when:%Y-%m-%d_%H-%M-%S}.csv"


def save_csv(nets, folder, when, min_rssi):
    """Salva una riga per BSSID; il nome del file contiene data e ora della scansione."""
    folder = Path(folder)
    folder.mkdir(parents=True, exist_ok=True)
    path = folder / csv_filename(when)
    with open(path, "w", newline="", encoding="utf-8-sig") as f:
        write_csv(f, nets, when, min_rssi)
    return path


def time_from_filename(path):
    m = re.search(r"(\d{4}-\d{2}-\d{2})_(\d{2})-(\d{2})-(\d{2})", Path(path).name)
    return f"{m.group(1)} {m.group(2)}:{m.group(3)}:{m.group(4)}" if m else ""


def load_csv(path):
    """Legge un salvataggio: (data/ora, [Network])."""
    nets, when = [], ""

    def num(text, conv=int, default=0):
        try:
            return conv(text)
        except (TypeError, ValueError):
            return default

    with open(path, newline="", encoding="utf-8-sig") as f:
        for row in csv.DictReader(f):
            freq = num(row.get("Frequenza MHz"))
            if band_of(freq) is None:
                continue
            when = when or row.get("Data/ora", "")
            nets.append(Network(
                row.get("SSID", ""), row.get("BSSID", ""), num(row.get("Segnale dBm"), default=FLOOR_DBM),
                freq, num(row.get("Larghezza MHz"), default=20), num(row.get("Centro MHz")),
                row.get("Standard", ""), num(row.get("Max PHY Mbps"), float, 0.0),
                num(row.get("Stream")), num(row.get("MCS max"), default=-1),
                num(row.get("Utilizzo canale %"), float, -1.0), num(row.get("Stazioni"), default=-1)))
    return when or time_from_filename(path), nets


def list_saved_scans(folder):
    return sorted(Path(folder).glob(f"{CSV_PREFIX}*.csv"))


# --------------------------------------------------------------------------
# Notifiche Microsoft Teams
# --------------------------------------------------------------------------

TEAMS_MAX_BYTES = 28000  # limite di Teams sulla dimensione di un messaggio
WEBHOOK_ENV = "WIFI_ANALYZER_TEAMS_WEBHOOK"


def channels_in(band, lo, hi):
    """Canali (griglia da 20 MHz) il cui centro cade in [lo, hi] MHz."""
    chans = BANDS[band]["channels"]
    inside = [c for c in chans if lo <= channel_to_freq(c, band) <= hi]
    if inside:
        return inside
    mid = (lo + hi) / 2
    return [min(chans, key=lambda c: abs(channel_to_freq(c, band) - mid))]


def channel_range_text(band, lo, hi):
    chans = channels_in(band, lo, hi)
    return f"ch {chans[0]}" if len(chans) == 1 else f"ch {chans[0]}-{chans[-1]}"


def overlap_hotspots(radios, min_rssi, max_overlaps):
    """Zone dove si sovrappongono piu' di max_overlaps radio (il numero sulla barra rossa).

    Ritorna (hotspot, chiavi) dove hotspot = [dict(band, lo, hi, count, names)] con le
    zone contigue unite, e chiavi = {(banda, canale)} dei canali coinvolti.
    """
    hot, keys = [], set()
    for band in BANDS:
        strong = [n for n in radios if n.band == band and n.rssi >= min_rssi]
        cur = None
        for lo, hi, count in congestion_segments(strong):
            if count <= max_overlaps:
                cur = None
            elif cur is not None and cur["hi"] == lo:
                cur["hi"], cur["count"] = hi, max(cur["count"], count)
            else:
                cur = dict(band=band, lo=lo, hi=hi, count=count)
                hot.append(cur)
        for h in hot:
            if h["band"] == band and "names" not in h:
                involved = sorted((n for n in strong if n.low < h["hi"] and n.high > h["lo"]),
                                  key=lambda n: -n.rssi)
                h["names"] = [n.name for n in involved]
                keys |= {(band, c) for c in channels_in(band, h["lo"], h["hi"])}
    return hot, keys


def band_report_lines(radios, min_rssi):
    lines = []
    for band, spec in BANDS.items():
        nets = [n for n in radios if n.band == band]
        if not nets:
            continue
        strong = [n for n in nets if n.rssi >= min_rssi]
        text = f"**{spec['title']}**: {len(nets)} reti"
        segs = congestion_segments(strong)
        if segs:
            lo, hi, count = max(segs, key=lambda s: s[2])
            text += f", max {count} reti sovrapposte su {channel_range_text(band, lo, hi)}"
        util = channel_utilization(strong)
        if util:
            f_max = max(util, key=util.get)
            text += f", utilizzo max {util[f_max]:.0f}% (ch {freq_to_channel(f_max)})"
        lines.append(text)
    return lines or ["Nessuna rete rilevata."]


def render_chart_b64(radios, min_rssi, max_len):
    """Grafico compatto per Teams come (mime, base64) non piu' lungo di max_len, o None.

    Senza le etichette delle reti (sono gia' nel testo del messaggio); prova la larghezza
    massima possibile, prima come PNG a palette (ottimo per colori piatti) poi come JPEG.
    """
    from PIL import Image  # dipendenza di matplotlib

    bands = [b for b in BANDS if any(n.band == b for n in radios)] or list(BANDS)
    fig = Figure(figsize=(10, 2.2 * len(bands) + 0.3), layout="constrained")
    draw_bands(fig, radios, bands, min_rssi, fontsize=11, show_labels=False)
    # si renderizza direttamente alla risoluzione finale: il testo resta nitido e
    # comprime molto meglio che ridimensionando un'immagine grande
    for dpi in (100, 90, 80, 72, 64, 56, 48):
        buf = io.BytesIO()
        fig.savefig(buf, format="png", dpi=dpi)
        im = Image.open(buf).convert("RGB")
        candidates = []
        for colors in (64, 32):  # meno colori renderebbe indistinguibili le reti
            out = io.BytesIO()
            im.quantize(colors=colors, method=Image.Quantize.FASTOCTREE,
                        dither=Image.Dither.NONE).save(out, "PNG", optimize=True)
            candidates.append(("image/png", out.getvalue()))
        for quality in (60, 45):
            out = io.BytesIO()
            im.save(out, "JPEG", quality=quality, optimize=True)
            candidates.append(("image/jpeg", out.getvalue()))
        for mime, data in candidates:
            b64 = base64.b64encode(data).decode("ascii")
            if len(b64) <= max_len:
                return mime, b64
    return None


def build_teams_message(kind, radios, when, min_rssi, hot=None, max_overlaps=None, image=True):
    """Messaggio Teams (Adaptive Card) per kind = "report" | "alert" | "test"."""
    radios = [dataclasses.replace(n, overlaps=[]) for n in radios]
    compute_overlaps(radios, min_rssi)
    stamp = f"{when:%d/%m/%Y %H:%M}  -  PC {socket.gethostname()}"
    body = []
    if kind == "alert":
        body.append(dict(type="TextBlock", text=f"⚠ Wi-Fi: canali con piu' di {max_overlaps} "
                                                  "reti sovrapposte", weight="Bolder", size="Medium",
                         color="Attention", wrap=True))
    elif kind == "test":
        body.append(dict(type="TextBlock", text="Wi-Fi Analyzer: messaggio di prova",
                         weight="Bolder", size="Medium", wrap=True))
    else:
        body.append(dict(type="TextBlock", text="Wi-Fi Analyzer: riepilogo periodico",
                         weight="Bolder", size="Medium", wrap=True))
    body.append(dict(type="TextBlock", text=stamp, isSubtle=True, spacing="None", wrap=True))
    if kind == "alert":
        for h in hot or []:
            names = ", ".join(h["names"][:6]) + (" ..." if len(h["names"]) > 6 else "")
            body.append(dict(type="TextBlock", wrap=True,
                             text=f"**{BANDS[h['band']]['title']} "
                                  f"{channel_range_text(h['band'], h['lo'], h['hi'])}**: "
                                  f"{h['count']} reti sovrapposte ({names})"))
    for i, line in enumerate(band_report_lines(radios, min_rssi)):
        body.append(dict(type="TextBlock", text=line, wrap=True,
                         spacing="Medium" if i == 0 else "Small"))

    def payload(blocks):
        card = {"$schema": "http://adaptivecards.io/schemas/adaptive-card.json",
                "type": "AdaptiveCard", "version": "1.4", "msteams": {"width": "Full"},
                "body": blocks}
        return {"type": "message", "attachments": [
            {"contentType": "application/vnd.microsoft.card.adaptive", "contentUrl": None,
             "content": card}]}

    if image and radios:
        budget = TEAMS_MAX_BYTES - len(json.dumps(payload(body))) - 300
        chart = render_chart_b64(radios, min_rssi, budget) if budget > 4000 else None
        if chart:
            body.append(dict(type="Image", url=f"data:{chart[0]};base64,{chart[1]}", size="Stretch",
                             altText="Grafico canali Wi-Fi"))
        else:
            body.append(dict(type="TextBlock", isSubtle=True, wrap=True,
                             text="(grafico omesso: non rientra nel limite di dimensione di Teams)"))
    return payload(body)


def post_teams(url, message, timeout=20):
    data = json.dumps(message).encode("utf-8")
    req = urllib.request.Request(url, data=data, method="POST",
                                 headers={"Content-Type": "application/json"})
    try:
        with urllib.request.urlopen(req, timeout=timeout) as resp:
            return f"HTTP {resp.status}, {len(data) // 1024} KB"
    except urllib.error.HTTPError as e:
        detail = e.read().decode("utf-8", "replace")[:300]
        raise RuntimeError(f"Teams ha risposto HTTP {e.code}: {detail}") from None
    except urllib.error.URLError as e:
        raise RuntimeError(f"Impossibile contattare Teams: {e.reason}") from None


class Notifier:
    """Riepilogo periodico e avviso canali affollati su Teams (usato da GUI e web service).

    on_result(kind, ok, testo) viene chiamata dal thread che esegue l'invio.
    """

    def __init__(self, settings, on_result):
        self.settings = settings
        self.on_result = on_result
        self.last_report = time.time()  # il primo riepilogo parte dopo N ore
        self.last_alert = 0.0
        self.alerted_keys = set()       # canali (banda, ch) gia' segnalati e ancora affollati

    def webhook_url(self):
        return self.settings["teams_webhook"].strip() or os.environ.get(WEBHOOK_ENV, "").strip()

    def settings_changed(self, old, new):
        if new.get("report_enabled") and not old.get("report_enabled"):
            self.last_report = time.time()
        if new.get("alert_threshold", old.get("alert_threshold")) != old.get("alert_threshold"):
            self.alerted_keys = set()

    def check(self, raw, min_rssi):
        """Dopo ogni scansione live: riepilogo periodico e avviso canali affollati."""
        s = self.settings
        if not self.webhook_url():
            return
        now = time.time()
        radios = group_radios(raw)
        compute_overlaps(radios, min_rssi)
        if s["alert_enabled"]:
            hot, keys = overlap_hotspots(radios, min_rssi, s["alert_threshold"])
            self.alerted_keys &= keys  # un canale tornato sotto soglia potra' essere risegnalato
            if keys - self.alerted_keys and now - self.last_alert >= s["alert_cooldown_min"] * 60:
                self.last_alert = now
                self.alerted_keys = keys
                self.send("alert", radios, min_rssi, hot)
        if s["report_enabled"] and now - self.last_report >= s["report_hours"] * 3600:
            self.last_report = now
            self.send("report", radios, min_rssi)

    def send(self, kind, radios, min_rssi, hot=None, url=None, image=None):
        """Prepara il messaggio (con il grafico) e lo invia in un thread. False se manca l'URL."""
        url = url or self.webhook_url()
        if not url:
            return False
        try:
            message = build_teams_message(kind, radios, datetime.now(), min_rssi, hot,
                                          self.settings["alert_threshold"],
                                          self.settings["notify_image"] if image is None else image)
        except Exception as e:
            self.on_result(kind, False, f"Errore nella preparazione del messaggio: {e}")
            return True

        def worker():
            try:
                self.on_result(kind, True, post_teams(url, message))
            except Exception as e:
                self.on_result(kind, False, str(e))
        threading.Thread(target=worker, daemon=True).start()
        return True


# --------------------------------------------------------------------------
# Grafico
# --------------------------------------------------------------------------

_PALETTE = ["#1f77b4", "#ff7f0e", "#2ca02c", "#d62728", "#9467bd", "#8c564b",
            "#e377c2", "#17becf", "#bcbd22", "#7f7f7f", "#393b79", "#ad494a",
            "#637939", "#8c6d31", "#7b4173", "#3182bd", "#e6550d", "#31a354"]


def color_for(bssid):
    return _PALETTE[zlib.crc32(bssid.encode()) % len(_PALETTE)]


def bell_curve(net, points=160):
    """Campana che parte dal fondo scala ai bordi del canale e raggiunge l'RSSI al centro."""
    x = np.linspace(net.low, net.high, points)
    t = np.abs(x - net.center_freq) / (net.width / 2)
    shape = np.cos(np.pi / 2 * t ** 2)  # cima larga, fianchi morbidi, zero ai bordi
    y = FLOOR_DBM + (net.rssi - FLOOR_DBM) * shape
    return x, y


def net_label(n):
    label = f"{n.name}  [{n.channel}]"
    return "⚠ " + label if n.overlaps else label


def layout_labels(nets, fig, n_axes, fmin, fmax, fs):
    """Posiziona le etichette (n.label_x, n.label_y) impilando quelle che si toccherebbero
    e tenendole dentro l'asse. Ritorna lo step verticale in dB."""
    pts_per_mhz = max(fig.get_figwidth() * 72 - 8 * fs, 100) / (fmax - fmin)
    pts_per_db = max(fig.get_figheight() * 72 / n_axes - 6 * fs, 60) / (TOP_DBM - FLOOR_DBM)
    step = fs * 1.35 / pts_per_db
    placed = []  # (x, y, mezza larghezza in MHz)
    for n in sorted(nets, key=lambda n: -n.rssi):
        half = len(net_label(n)) * fs * 0.3 / pts_per_mhz
        x = min(max(n.center_freq, fmin + half), fmax - half)
        y = n.rssi + 0.3 * step
        while True:
            clash = [py for px, py, ph in placed if abs(px - x) < ph + half and abs(py - y) < step]
            if not clash:
                break
            y = max(clash) + step * 1.001  # margine: evita loop infinito per arrotondamenti
        placed.append((x, y, half))
        n.label_x, n.label_y = x, y
    return step


def draw_bands(fig, nets, bands, min_rssi, selected=None, fontsize=11, show_util=True,
               show_labels=True):
    fig.clear()
    if not bands:
        return
    fs = fontsize
    axes = fig.subplots(len(bands), 1, squeeze=False)[:, 0]
    sel = next((n for n in nets if n.bssid == selected), None)
    related = ({sel.bssid} | {o.bssid for o, _, _ in sel.overlaps}) if sel else set()

    for ax, key in zip(axes, bands):
        spec = BANDS[key]
        span = spec["fmax"] - spec["fmin"]
        band_nets = sorted((n for n in nets if n.band == key), key=lambda n: n.rssi)
        strong = [n for n in band_nets if n.rssi >= min_rssi]
        step = layout_labels(band_nets, fig, len(bands), spec["fmin"], spec["fmax"], fs)
        # spazio extra per le etichette impilate, al massimo meta' della scala in dB
        top = max([TOP_DBM] + [n.label_y + 1.6 * step for n in band_nets if show_labels])
        top = min(top, TOP_DBM + 0.5 * (TOP_DBM - FLOOR_DBM))
        axis_pts = max(fig.get_figheight() * 72 / len(bands) - 6 * fs, 60)
        tick = next((s for s in (10, 20, 30) if s * axis_pts / (top - FLOOR_DBM) >= 1.8 * fs), 50)

        ax.set_xlim(spec["fmin"], spec["fmax"])
        ax.set_ylim(FLOOR_DBM, top)
        ax.set_yticks(range(FLOOR_DBM, TOP_DBM + 1, tick))  # niente tacche nello spazio etichette
        ax.set_ylabel("Segnale (dBm)", fontsize=fs)
        ax.tick_params(axis="y", labelsize=fs - 1)
        ax.set_xticks([channel_to_freq(c, key) for c in spec["labels"]])
        ax.set_xticklabels([str(c) for c in spec["labels"]], fontsize=fs - 1,
                           rotation=90 if key != "2.4" else 0)
        ax.set_xticks([channel_to_freq(c, key) for c in spec["channels"]], minor=True)
        if show_labels:  # la versione compatta (Teams) evita dettagli che pesano in KB
            ax.grid(axis="y", alpha=0.3)
            ax.grid(axis="x", which="major", alpha=0.15)
        ax.axhline(min_rssi, color="#999999", lw=0.8, ls=":")

        if key == "5" and show_labels:
            for lo, hi in DFS_RANGES:
                ax.axvspan(lo, hi, color="#000000", alpha=0.04, lw=0)
                ax.text((lo + hi) / 2, top - 1, "DFS", ha="center", va="top",
                        fontsize=fs - 1, color="#777777")

        for n in band_nets:
            c = color_for(n.bssid)
            weak = n.rssi < min_rssi
            faded = sel is not None and n.bssid not in related
            is_sel = sel is not None and n.bssid == sel.bssid
            line_alpha = 0.2 if (faded or weak) else 1.0
            x, y = bell_curve(n)
            ax.fill_between(x, FLOOR_DBM, y, color=c, lw=0,
                            alpha=0.04 if faded else (0.38 if is_sel else 0.16))
            ax.plot(x, y, color=c, lw=3 if is_sel else 1.6, alpha=line_alpha,
                    ls="--" if weak else "-")
            if not show_labels:
                continue
            moved = n.label_y - n.rssi > step or abs(n.label_x - n.center_freq) > 1
            ann = ax.annotate(net_label(n), (n.center_freq, n.rssi), xytext=(n.label_x, n.label_y),
                              ha="center", va="bottom", fontsize=fs - 1, color=c, alpha=line_alpha,
                              fontweight="bold" if is_sel else "normal", clip_on=True,
                              arrowprops=dict(arrowstyle="-", color=c, lw=0.6, alpha=line_alpha)
                              if moved else None)
            ann.set_in_layout(False)  # etichette fuori scala non devono schiacciare il layout
            if ann.arrow_patch is not None:
                ann.arrow_patch.set_clip_box(ax.bbox)
                ann.arrow_patch.set_clip_on(True)

        # Barra rossa in basso: zone del canale con 2+ radio sovrapposte
        for lo, hi, count in congestion_segments(strong):
            ax.axvspan(lo, hi, ymin=0, ymax=0.05, color="#d62728", lw=0,
                       alpha=min(0.3 + 0.15 * (count - 2), 0.95))
            if hi - lo >= span / 60:
                ax.text((lo + hi) / 2, FLOOR_DBM + 0.025 * (top - FLOOR_DBM), str(count),
                        ha="center", va="center", fontsize=fs - 2, color="white", fontweight="bold")

        # Riquadri colorati sopra la barra rossa: utilizzo del canale primario (BSS Load)
        util = channel_utilization(strong)
        if show_util:
            # a 2.4 GHz i canali distano 5 MHz: riquadri larghi un passo per non coprirsi;
            # a 5/6 GHz larghi 20 MHz (ma almeno visibili anche nella banda da 1200 MHz)
            half = 2.4 if key == "2.4" else max(10, span / 120)
            for f, u in util.items():
                ax.axvspan(f - half + 0.5, f + half - 0.5, ymin=0.06, ymax=0.13,
                           color=util_color(u), lw=0, alpha=0.9)
                if 2 * half >= span / 70:
                    ax.text(f, FLOOR_DBM + 0.095 * (top - FLOOR_DBM), f"{u:.0f}%", ha="center",
                            va="center", fontsize=max(fs - 3, 6), color="black", clip_on=True)

        n_ovl = sum(1 for n in strong if n.overlaps)
        title = f"{spec['title']}  ({spec['fmin']}-{spec['fmax']} MHz)  -  {len(band_nets)} reti"
        if strong:
            title += f", {n_ovl} con sovrapposizioni"
        if util:
            f_max = max(util, key=util.get)
            title += f", utilizzo max {util[f_max]:.0f}% (ch {freq_to_channel(f_max)})"
        ax.set_title(title, fontsize=fs + 1, loc="left")
        if not band_nets:
            ax.text(0.5, 0.5, "Nessuna rete rilevata", transform=ax.transAxes,
                    ha="center", va="center", color="#999999", fontsize=fs)
    if show_labels:
        xlabel = "Canale  (barra rossa = canali sovrapposti, il numero indica quante reti"
        if show_util:
            xlabel += ";  riquadri = % di tempo canale occupato, dichiarata dagli AP"
        axes[-1].set_xlabel(xlabel + ")", fontsize=fs)


# --------------------------------------------------------------------------
# Impostazioni persistenti
# --------------------------------------------------------------------------

SETTINGS_PATH = Path.home() / ".wifi_analyzer.json"
DEFAULT_SETTINGS = dict(font_size=11, interval=15, min_rssi=-90, group=True, show_util=True,
                        hidden_columns=[],
                        teams_webhook="", notify_image=True,
                        report_enabled=False, report_hours=4.0,
                        alert_enabled=False, alert_threshold=4, alert_cooldown_min=30,
                        save_csv=False, save_dir=str(Path.cwd() / "wifi_logs"), play_speed=1.0,
                        auto_scan=True)


def load_settings():
    settings = dict(DEFAULT_SETTINGS)
    try:
        settings.update(json.loads(SETTINGS_PATH.read_text(encoding="utf-8")))
    except (OSError, ValueError):
        pass
    return settings


def store_settings(settings):
    try:
        SETTINGS_PATH.write_text(json.dumps(settings, indent=2), encoding="utf-8")
    except OSError:
        pass


# --------------------------------------------------------------------------
# Interfaccia grafica Tk
# --------------------------------------------------------------------------

FONT_SIZES = (8, 9, 10, 11, 12, 13, 14, 16, 18, 20, 24)

TABLE_COLUMNS = [  # id, intestazione, larghezza a font 10
    ("ssid", "SSID", 200), ("bssid", "BSSID", 140), ("band", "Banda", 70),
    ("channel", "Canale", 60), ("width", "Larghezza", 80), ("center", "Centro MHz", 90),
    ("rssi", "Segnale dBm", 95), ("std", "Standard", 110), ("rate", "Max PHY", 90),
    ("nss", "Stream", 95), ("util", "Utilizzo canale", 115), ("sta", "Stazioni", 75),
    ("novl", "Sovrapp.", 75), ("detail", "Sovrapposta con", 500)]

SORT_KEYS = {
    "ssid": lambda n: n.name.lower(), "bssid": lambda n: n.bssid,
    "band": lambda n: n.primary_freq, "channel": lambda n: n.primary_freq,
    "width": lambda n: n.width, "center": lambda n: n.center_freq,
    "rssi": lambda n: n.rssi, "std": lambda n: n.standard,
    "rate": lambda n: n.max_rate, "nss": lambda n: (n.nss, n.mcs),
    "util": lambda n: n.util, "sta": lambda n: n.stations,
    "novl": lambda n: len(n.overlaps), "detail": lambda n: len(n.overlaps),
}


def row_tag(n, min_rssi):
    """Colore della riga in tabella: weak / partial / cochannel / ok."""
    if n.rssi < min_rssi:
        return "weak"
    if any(k == "parziale" for _, k, _ in n.overlaps):
        return "partial"
    return "cochannel" if n.overlaps else "ok"


def row_values(n):
    """Celle della tabella nello stesso ordine di TABLE_COLUMNS."""
    return (n.name, n.bssid, BANDS[n.band]["title"], n.channel, f"{n.width} MHz",
            n.center_freq, n.rssi, n.standard, n.rate_text, n.stream_text,
            n.util_text, n.stations_text, len(n.overlaps), overlap_summary(n))


class App:
    def __init__(self, scanner, settings, playback_dir=None):
        import tkinter as tk
        import tkinter.font as tkfont
        from tkinter import filedialog, messagebox, ttk
        from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk
        self.tk, self.ttk, self.tkfont = tk, ttk, tkfont
        self.filedialog, self.messagebox = filedialog, messagebox

        self.scanner = scanner
        self.settings = settings
        self.root = root = tk.Tk()
        root.geometry("1500x1000")

        self.raw = []           # reti dell'ultima scansione / del file in playback
        self.nets = []          # reti mostrate (eventualmente raggruppate per AP)
        self.selected = None
        self.sort = ("rssi", True)
        self.mode = "live"
        self.scanning = False
        self.scan_token = 0     # invalida i risultati di scansioni avviate prima di un cambio modalita'
        self.after_id = None
        self.results = queue.Queue()
        self.pb_files, self.pb_cache, self.pb_index, self.pb_after = [], {}, 0, None
        self.notify_results = queue.Queue()
        self.notifier = Notifier(settings, lambda *result: self.notify_results.put(result))

        self.font_var = tk.IntVar(value=settings["font_size"])
        self.auto_var = tk.BooleanVar(value=settings["auto_scan"])
        self.interval_var = tk.IntVar(value=settings["interval"])
        self.thr_var = tk.IntVar(value=settings["min_rssi"])
        self.group_var = tk.BooleanVar(value=settings["group"])
        self.util_var = tk.BooleanVar(value=settings["show_util"])
        self.save_var = tk.BooleanVar(value=settings["save_csv"])
        self.speed_var = tk.DoubleVar(value=settings["play_speed"])
        self.band_vars = {k: tk.BooleanVar(value=True) for k in BANDS}
        hidden = set(settings["hidden_columns"])
        self.col_vars = {cid: tk.BooleanVar(value=cid not in hidden) for cid, _t, _w in TABLE_COLUMNS}

        self._build_menu()
        self._build_toolbar()
        self._build_playback_bar()
        self._build_body(FigureCanvasTkAgg, NavigationToolbar2Tk)
        self.apply_font()

        self.thr_var.trace_add("write", lambda *_: self.refresh())
        self.auto_var.trace_add("write", lambda *_: self.schedule_next())
        self.save_var.trace_add("write", lambda *_: self._update_save_label())
        for seq, delta in (("<Control-plus>", 1), ("<Control-equal>", 1), ("<Control-KP_Add>", 1),
                           ("<Control-minus>", -1), ("<Control-KP_Subtract>", -1)):
            root.bind(seq, lambda _e, d=delta: self.bump_font(d))
        root.bind("<Escape>", self.on_escape)
        root.bind("<Left>", lambda _e: self.step(-1))
        root.bind("<Right>", lambda _e: self.step(1))
        root.bind("<space>", lambda _e: self.toggle_play() if self.mode == "playback" else None)
        root.protocol("WM_DELETE_WINDOW", self.on_close)
        root.after(150, self.poll)

        if playback_dir is None or not self.enter_playback(playback_dir):
            self.enter_live()

    # ---------------------------------------------------------------- layout
    def _build_menu(self):
        tk = self.tk
        menubar = tk.Menu(self.root)
        fm = tk.Menu(menubar, tearoff=0)
        fm.add_command(label="Apri cartella di playback...", command=self.choose_playback)
        fm.add_command(label="Torna alla scansione live", command=self.enter_live)
        fm.add_separator()
        fm.add_checkbutton(label="Salva ogni scansione su CSV", variable=self.save_var)
        fm.add_command(label="Cartella salvataggi...", command=self.choose_save_dir)
        fm.add_separator()
        fm.add_command(label="Esci", command=self.on_close)
        menubar.add_cascade(label="File", menu=fm)

        vm = tk.Menu(menubar, tearoff=0)
        sizes = tk.Menu(vm, tearoff=0)
        for s in FONT_SIZES:
            sizes.add_radiobutton(label=f"{s} pt", value=s, variable=self.font_var,
                                  command=self.apply_font)
        vm.add_cascade(label="Dimensione testo", menu=sizes)
        vm.add_command(label="Testo piu' grande", accelerator="Ctrl +",
                       command=lambda: self.bump_font(1))
        vm.add_command(label="Testo piu' piccolo", accelerator="Ctrl -",
                       command=lambda: self.bump_font(-1))
        vm.add_separator()
        vm.add_checkbutton(label="Raggruppa SSID dello stesso AP", variable=self.group_var,
                           command=self.refresh)
        vm.add_checkbutton(label="Mostra utilizzo canale (BSS Load)", variable=self.util_var,
                           command=self.refresh)
        # Colonne della tabella: nasconderle cambia solo la vista, il CSV le contiene sempre
        cols = tk.Menu(vm, tearoff=0)
        for cid, text, _w in TABLE_COLUMNS:
            cols.add_checkbutton(label=text, variable=self.col_vars[cid], command=self.apply_columns)
        cols.add_separator()
        cols.add_command(label="Mostra tutte", command=lambda: self.apply_columns(show_all=True))
        vm.add_cascade(label="Colonne tabella", menu=cols)
        for key in BANDS:
            vm.add_checkbutton(label=f"Mostra {BANDS[key]['title']}", variable=self.band_vars[key],
                               command=self.refresh)
        menubar.add_cascade(label="Visualizza", menu=vm)

        nm = tk.Menu(menubar, tearoff=0)
        nm.add_command(label="Impostazioni notifiche Teams...", command=self.open_notify_dialog)
        nm.add_command(label="Invia riepilogo adesso", command=lambda: self.send_notification("report"))
        menubar.add_cascade(label="Notifiche", menu=nm)
        self.root.config(menu=menubar)

    def _build_toolbar(self):
        tk, ttk = self.tk, self.ttk
        bar = ttk.Frame(self.root, padding=4)
        bar.pack(side=tk.TOP, fill=tk.X)
        self.btn_scan = ttk.Button(bar, text="Scansiona ora", command=self.start_scan)
        self.btn_scan.pack(side=tk.LEFT)
        self.chk_auto = ttk.Checkbutton(bar, text="Aggiorna ogni", variable=self.auto_var)
        self.chk_auto.pack(side=tk.LEFT, padx=(12, 2))
        self.spin_interval = ttk.Spinbox(bar, from_=5, to=600, increment=5, width=5,
                                         textvariable=self.interval_var)
        self.spin_interval.pack(side=tk.LEFT)
        ttk.Label(bar, text="s").pack(side=tk.LEFT, padx=(2, 12))
        self.chk_save = ttk.Checkbutton(bar, text="Salva CSV", variable=self.save_var)
        self.chk_save.pack(side=tk.LEFT)
        self.lbl_save = ttk.Label(bar, foreground="#555555", cursor="hand2")
        self.lbl_save.pack(side=tk.LEFT, padx=(2, 12))
        self.lbl_save.bind("<Button-1>", lambda _e: self.choose_save_dir())
        self.live_widgets = [self.btn_scan, self.chk_auto, self.spin_interval, self.chk_save]

        ttk.Label(bar, text="Ignora sotto").pack(side=tk.LEFT)
        ttk.Spinbox(bar, from_=-100, to=-30, increment=5, width=5,
                    textvariable=self.thr_var).pack(side=tk.LEFT, padx=2)
        ttk.Label(bar, text="dBm").pack(side=tk.LEFT, padx=(0, 12))
        ttk.Checkbutton(bar, text="Raggruppa AP", variable=self.group_var,
                        command=self.refresh).pack(side=tk.LEFT, padx=(0, 12))
        for key in BANDS:
            ttk.Checkbutton(bar, text=BANDS[key]["title"], variable=self.band_vars[key],
                            command=self.refresh).pack(side=tk.LEFT, padx=2)
        self.status = ttk.Label(bar, text="Pronto", foreground="#555555")
        self.status.pack(side=tk.RIGHT)
        self.lbl_notify = ttk.Label(bar, text="", foreground="#555555")
        self.lbl_notify.pack(side=tk.RIGHT, padx=(0, 16))
        self._update_save_label()

    def _build_playback_bar(self):
        tk, ttk = self.tk, self.ttk
        self.pb_bar = bar = ttk.Frame(self.root, padding=4)
        ttk.Label(bar, text="PLAYBACK", foreground="#b03030").pack(side=tk.LEFT, padx=(0, 8))
        ttk.Button(bar, text="⏮", width=3, command=lambda: self.show_frame(0)).pack(side=tk.LEFT)
        ttk.Button(bar, text="◀", width=3, command=lambda: self.step(-1)).pack(side=tk.LEFT)
        self.btn_play = ttk.Button(bar, text="▶ Play", width=8, command=self.toggle_play)
        self.btn_play.pack(side=tk.LEFT)
        ttk.Button(bar, text="▶", width=3, command=lambda: self.step(1)).pack(side=tk.LEFT)
        ttk.Button(bar, text="⏭", width=3,
                   command=lambda: self.show_frame(len(self.pb_files) - 1)).pack(side=tk.LEFT)
        ttk.Label(bar, text="  s/passo").pack(side=tk.LEFT)
        ttk.Spinbox(bar, from_=0.2, to=30, increment=0.2, width=5,
                    textvariable=self.speed_var).pack(side=tk.LEFT, padx=(2, 8))
        ttk.Button(bar, text="Aggiorna elenco", command=self.reload_playback).pack(side=tk.RIGHT)
        ttk.Button(bar, text="Torna al live", command=self.enter_live).pack(side=tk.RIGHT, padx=4)
        self.pb_label = ttk.Label(bar, text="")
        self.pb_label.pack(side=tk.RIGHT, padx=8)
        self.pb_scale = tk.Scale(bar, from_=0, to=0, orient=tk.HORIZONTAL, showvalue=False,
                                 command=self.on_scale)
        self.pb_scale.pack(side=tk.LEFT, fill=tk.X, expand=True, padx=8)

    def _build_body(self, FigureCanvasTkAgg, NavigationToolbar2Tk):
        tk, ttk = self.tk, self.ttk
        self.legend = ttk.Label(
            self.root, padding=(6, 2), foreground="#555555",
            text="Verde: canale libero  |  Giallo: stesso canale di altre reti (si dividono il tempo"
                 " di trasmissione)  |  Rosso: sovrapposizione parziale (interferenza)  |  "
                 "Utilizzo canale: % di tempo in cui l'AP sente il canale occupato (verde <30, giallo <50,"
                 " arancio <70, rosso oltre), solo per gli AP che lo dichiarano  |  "
                 "Clicca una riga per evidenziarla, Esc per deselezionare")
        self.legend.pack(side=tk.BOTTOM, fill=tk.X)

        self.panes = ttk.PanedWindow(self.root, orient=tk.VERTICAL)
        self.panes.pack(fill=tk.BOTH, expand=True)

        plot_frame = ttk.Frame(self.panes)
        self.fig = Figure(figsize=(14, 9), layout="constrained")
        self.canvas = FigureCanvasTkAgg(self.fig, master=plot_frame)
        NavigationToolbar2Tk(self.canvas, plot_frame).update()
        self.canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
        self.panes.add(plot_frame, weight=3)

        table_frame = ttk.Frame(self.panes)
        self.tree = tree = ttk.Treeview(table_frame, columns=[c[0] for c in TABLE_COLUMNS],
                                        show="headings", height=8)
        for cid, text, _w in TABLE_COLUMNS:
            tree.heading(cid, text=text, command=lambda c=cid: self.sort_by(c))
            tree.column(cid, anchor=tk.W if cid in ("ssid", "bssid", "detail") else tk.CENTER,
                        stretch=(cid == "detail"))
        tree.tag_configure("ok", background="#dff5df")
        tree.tag_configure("cochannel", background="#fff2c2")
        tree.tag_configure("partial", background="#f8d3d3")
        tree.tag_configure("weak", foreground="#999999")
        sb = ttk.Scrollbar(table_frame, orient=tk.VERTICAL, command=tree.yview)
        tree.configure(yscrollcommand=sb.set)
        tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        sb.pack(side=tk.RIGHT, fill=tk.Y)
        tree.bind("<<TreeviewSelect>>", self.on_select)
        self.panes.add(table_frame, weight=1)
        self.apply_columns()

    def apply_columns(self, show_all=False):
        if show_all:
            for var in self.col_vars.values():
                var.set(True)
        shown = [cid for cid, _t, _w in TABLE_COLUMNS if self.col_vars[cid].get()]
        if not shown:  # una tabella senza colonne non ha senso: tieni almeno l'SSID
            self.col_vars["ssid"].set(True)
            shown = ["ssid"]
        self.tree.configure(displaycolumns=shown)
        self.settings["hidden_columns"] = [cid for cid in self.col_vars if cid not in shown]

    # ---------------------------------------------------------------- font
    def apply_font(self):
        fs = self.font_var.get()
        self.settings["font_size"] = fs
        for name in ("TkDefaultFont", "TkTextFont", "TkHeadingFont", "TkMenuFont"):
            try:
                self.tkfont.nametofont(name).configure(size=fs)
            except Exception:
                pass
        line = self.tkfont.nametofont("TkDefaultFont").metrics("linespace")
        self.ttk.Style().configure("Treeview", rowheight=line + 6)
        for cid, _text, w in TABLE_COLUMNS:
            self.tree.column(cid, width=int(w * max(fs, 10) / 10))
        self.legend.configure(wraplength=max(self.root.winfo_width() - 20, 800))
        self.refresh()

    def bump_font(self, delta):
        sizes = FONT_SIZES
        cur = self.font_var.get()
        idx = min(range(len(sizes)), key=lambda i: abs(sizes[i] - cur))
        self.font_var.set(sizes[max(0, min(len(sizes) - 1, idx + delta))])
        self.apply_font()

    # ---------------------------------------------------------------- vista
    def threshold(self):
        try:
            return int(self.thr_var.get())
        except (self.tk.TclError, ValueError):
            return FLOOR_DBM

    def refresh(self):
        self.nets = group_radios(self.raw) if self.group_var.get() else list(self.raw)
        compute_overlaps(self.nets, self.threshold())
        if self.selected and all(n.bssid != self.selected for n in self.nets):
            self.selected = None
        bands = [k for k in BANDS if self.band_vars[k].get()]
        draw_bands(self.fig, self.nets, bands, self.threshold(), self.selected, self.font_var.get(),
                   self.util_var.get())
        self.canvas.draw_idle()
        self.fill_table()

    def fill_table(self):
        tree, (key, rev), thr = self.tree, self.sort, self.threshold()
        tree.delete(*tree.get_children())
        for n in sorted(self.nets, key=SORT_KEYS[key], reverse=rev):
            if not self.band_vars[n.band].get():
                continue
            tree.insert("", self.tk.END, iid=n.bssid, tags=(row_tag(n, thr),), values=row_values(n))
        if self.selected and tree.exists(self.selected):
            tree.selection_set(self.selected)

    def sort_by(self, col):
        key, rev = self.sort
        self.sort = (col, not rev if key == col
                     else col in ("rssi", "rate", "nss", "util", "sta", "novl", "detail"))
        self.fill_table()

    def on_select(self, _event):
        sel = self.tree.selection()
        new = sel[0] if sel else None
        if new != self.selected:
            self.selected = new
            self.refresh()

    def on_escape(self, _event):
        self.selected = None
        self.tree.selection_remove(*self.tree.selection())
        self.refresh()

    # ---------------------------------------------------------------- live
    def enter_live(self):
        if self.scanner is None:
            self.messagebox.showerror("Scansione non disponibile",
                                      "Nessuno scanner Wi-Fi disponibile su questo sistema.")
            return
        self.stop_play()
        self.pb_bar.pack_forget()
        self.mode = "live"
        for w in self.live_widgets:
            w.state(["!disabled"])
        self.root.title(f"WiFi Analyzer - {self.scanner.name}")
        self.raw = []
        self.refresh()
        self.status.config(text="Pronto")
        self.start_scan()

    def _update_save_label(self):
        self.settings["save_csv"] = self.save_var.get()
        folder = self.settings["save_dir"]
        self.lbl_save.config(text=f"in {folder}" if self.save_var.get() else "")

    def choose_save_dir(self):
        d = self.filedialog.askdirectory(title="Cartella dove salvare le scansioni",
                                         initialdir=self.settings["save_dir"], mustexist=False)
        if d:
            self.settings["save_dir"] = d
            self._update_save_label()

    def worker(self, token):
        try:
            self.results.put((token, "ok", self.scanner.scan(), datetime.now()))
        except Exception as e:  # riportato nella GUI
            self.results.put((token, "err", e, datetime.now()))

    def start_scan(self):
        if self.mode != "live":
            return
        if self.after_id:
            self.root.after_cancel(self.after_id)
            self.after_id = None
        if self.scanning:
            return
        self.scanning = True
        self.btn_scan.state(["disabled"])
        self.status.config(text="Scansione in corso...")
        threading.Thread(target=self.worker, args=(self.scan_token,), daemon=True).start()

    def schedule_next(self):
        if self.after_id:
            self.root.after_cancel(self.after_id)
            self.after_id = None
        if self.mode != "live" or self.scanning or not self.auto_var.get():
            return
        try:
            secs = max(5, int(self.interval_var.get()))
        except (self.tk.TclError, ValueError):
            secs = 15
        self.after_id = self.root.after(secs * 1000, self.start_scan)

    def poll(self):
        try:
            token, kind, payload, when = self.results.get_nowait()
        except queue.Empty:
            pass
        else:
            self.scanning = False
            if self.mode == "live":
                self.btn_scan.state(["!disabled"])
            if token != self.scan_token:
                self.start_scan()  # risultato di una scansione avviata prima del playback
            elif kind == "ok":
                msg = f"Ultima scansione {when:%H:%M:%S}  -  {len(payload)} BSSID"
                if self.save_var.get():
                    try:
                        path = save_csv(payload, self.settings["save_dir"], when, self.threshold())
                        msg += f"  -  salvata {path.name}"
                    except OSError as e:
                        msg += f"  -  ERRORE salvataggio: {e}"
                self.raw = payload
                self.refresh()
                self.status.config(text=msg)
                self.schedule_next()
                self.check_notifications()
            else:
                self.status.config(text="Errore di scansione")
                self.auto_var.set(False)
                self.messagebox.showerror("Errore scansione", str(payload))
        try:
            kind, ok, text = self.notify_results.get_nowait()
        except queue.Empty:
            pass
        else:
            label = {"report": "riepilogo", "alert": "avviso", "test": "prova"}[kind]
            if ok:
                self.lbl_notify.config(text=f"Teams: {label} inviato {datetime.now():%H:%M}",
                                       foreground="#2a7a2a")
            else:
                self.lbl_notify.config(text=f"Teams: errore invio {label}", foreground="#b03030")
            if kind == "test":
                (self.messagebox.showinfo if ok else self.messagebox.showerror)(
                    "Notifica Teams", f"Messaggio inviato ({text})." if ok else text)
        self.root.after(150, self.poll)

    # ---------------------------------------------------------------- notifiche
    def check_notifications(self):
        self.notifier.check(self.raw, self.threshold())

    def send_notification(self, kind, url=None, image=None):
        url = url or self.notifier.webhook_url()
        if not url:
            self.messagebox.showwarning("Notifica Teams",
                                        "Configura prima l'URL del webhook in Notifiche > Impostazioni.")
            return
        self.lbl_notify.config(text="Teams: invio in corso...", foreground="#555555")
        self.notifier.send(kind, group_radios(self.raw), self.threshold(), url=url, image=image)

    def open_notify_dialog(self):
        tk, ttk, s = self.tk, self.ttk, self.settings
        win = tk.Toplevel(self.root)
        win.title("Impostazioni notifiche Teams")
        win.transient(self.root)
        win.resizable(False, False)
        frm = ttk.Frame(win, padding=14)
        frm.pack(fill=tk.BOTH, expand=True)

        url_var = tk.StringVar(value=s["teams_webhook"])
        img_var = tk.BooleanVar(value=s["notify_image"])
        rep_var = tk.BooleanVar(value=s["report_enabled"])
        hours_var = tk.StringVar(value=str(s["report_hours"]))
        al_var = tk.BooleanVar(value=s["alert_enabled"])
        thr_var = tk.StringVar(value=str(s["alert_threshold"]))
        cool_var = tk.StringVar(value=str(s["alert_cooldown_min"]))

        ttk.Label(frm, text="URL del webhook Teams:").grid(row=0, column=0, sticky="w")
        ttk.Entry(frm, textvariable=url_var, width=80).grid(row=1, column=0, columnspan=4,
                                                           sticky="we", pady=(2, 2))
        ttk.Label(frm, foreground="#555555", wraplength=640, justify="left",
                  text="In Teams: sul canale scegli ... > Workflows > \"Post to a channel when a webhook "
                       "request is received\" (\"Pubblica in un canale quando viene ricevuta una "
                       "richiesta webhook\") e copia qui l'URL generato. Chi conosce l'URL puo' "
                       "scrivere nel canale: viene salvato in chiaro in " + str(SETTINGS_PATH) + ".",
                  ).grid(row=2, column=0, columnspan=4, sticky="w")
        if not s["teams_webhook"] and os.environ.get(WEBHOOK_ENV):
            ttk.Label(frm, foreground="#555555",
                      text=f"(vuoto: viene usato l'URL nella variabile {WEBHOOK_ENV})").grid(
                row=3, column=0, columnspan=4, sticky="w")
        ttk.Checkbutton(frm, text="Allega l'immagine del grafico (ridotta per il limite di ~28 KB di Teams)",
                        variable=img_var).grid(row=4, column=0, columnspan=4, sticky="w", pady=(8, 0))

        rep = ttk.LabelFrame(frm, text="Riepilogo periodico", padding=8)
        rep.grid(row=5, column=0, columnspan=4, sticky="we", pady=(10, 0))
        ttk.Checkbutton(rep, text="Invia un riepilogo ogni", variable=rep_var).pack(side=tk.LEFT)
        ttk.Spinbox(rep, from_=0.25, to=168, increment=0.5, width=6,
                    textvariable=hours_var).pack(side=tk.LEFT, padx=4)
        ttk.Label(rep, text="ore").pack(side=tk.LEFT)

        al = ttk.LabelFrame(frm, text="Avviso canali affollati", padding=8)
        al.grid(row=6, column=0, columnspan=4, sticky="we", pady=(10, 0))
        row = ttk.Frame(al)
        row.pack(fill=tk.X)
        ttk.Checkbutton(row, text="Avvisa quando un canale ha piu' di", variable=al_var).pack(side=tk.LEFT)
        ttk.Spinbox(row, from_=1, to=50, width=4, textvariable=thr_var).pack(side=tk.LEFT, padx=4)
        ttk.Label(row, text="reti sovrapposte").pack(side=tk.LEFT)
        row = ttk.Frame(al)
        row.pack(fill=tk.X, pady=(4, 0))
        ttk.Label(row, text="Non ripetere l'avviso prima di").pack(side=tk.LEFT)
        ttk.Spinbox(row, from_=1, to=1440, width=5, textvariable=cool_var).pack(side=tk.LEFT, padx=4)
        ttk.Label(row, text="minuti").pack(side=tk.LEFT)
        ttk.Label(al, foreground="#555555", wraplength=620, justify="left",
                  text="Si conta il numero mostrato sulla barra rossa: reti sopra la soglia \"Ignora sotto\", "
                       "unendo gli SSID dello stesso AP. L'avviso parte quando un canale supera la soglia "
                       "e si ripete solo se altri canali la superano o se torna sotto e poi di nuovo sopra.",
                  ).pack(fill=tk.X, pady=(6, 0))

        def read_values():
            try:
                values = dict(teams_webhook=url_var.get().strip(), notify_image=img_var.get(),
                              report_enabled=rep_var.get(),
                              report_hours=max(0.25, float(hours_var.get().replace(",", "."))),
                              alert_enabled=al_var.get(), alert_threshold=max(1, int(thr_var.get())),
                              alert_cooldown_min=max(1, int(cool_var.get())))
            except ValueError:
                self.messagebox.showerror("Notifiche", "Controlla i valori numerici.", parent=win)
                return None
            if values["teams_webhook"] and not values["teams_webhook"].lower().startswith("https://"):
                self.messagebox.showerror("Notifiche", "L'URL del webhook deve iniziare con https://",
                                          parent=win)
                return None
            return values

        def save():
            values = read_values()
            if values is None:
                return
            self.notifier.settings_changed(s, values)
            s.update(values)
            store_settings(s)
            win.destroy()

        def test():
            values = read_values()
            if values is None:
                return
            url = values["teams_webhook"] or os.environ.get(WEBHOOK_ENV, "").strip()
            if not url:
                self.messagebox.showwarning("Notifiche", "Inserisci l'URL del webhook.", parent=win)
                return
            # la prova usa le opzioni del dialogo anche se non ancora salvate
            self.send_notification("test", url=url, image=values["notify_image"])

        buttons = ttk.Frame(frm)
        buttons.grid(row=7, column=0, columnspan=4, sticky="e", pady=(14, 0))
        ttk.Button(buttons, text="Invia messaggio di prova", command=test).pack(side=tk.LEFT, padx=4)
        ttk.Button(buttons, text="Salva", command=save).pack(side=tk.LEFT, padx=4)
        ttk.Button(buttons, text="Annulla", command=win.destroy).pack(side=tk.LEFT, padx=4)
        win.grab_set()

    # ---------------------------------------------------------------- playback
    def choose_playback(self):
        d = self.filedialog.askdirectory(title="Cartella con i salvataggi da riprodurre",
                                         initialdir=self.settings["save_dir"])
        if d:
            self.enter_playback(d)

    def enter_playback(self, folder):
        files = list_saved_scans(folder)
        if not files:
            self.messagebox.showwarning("Playback", f"Nessun file {CSV_PREFIX}*.csv in\n{folder}")
            return False
        self.mode = "playback"
        self.scan_token += 1
        if self.after_id:
            self.root.after_cancel(self.after_id)
            self.after_id = None
        for w in self.live_widgets:
            w.state(["disabled"])
        self.pb_dir = Path(folder)
        self.pb_files = files
        self.pb_cache.clear()
        self.pb_scale.config(to=len(files) - 1)
        self.pb_bar.pack(side=self.tk.TOP, fill=self.tk.X, before=self.panes)
        self.root.title(f"WiFi Analyzer - Playback: {self.pb_dir}")
        self.show_frame(0)
        return True

    def reload_playback(self):
        current = self.pb_files[self.pb_index] if self.pb_files else None
        files = list_saved_scans(self.pb_dir)
        if not files:
            return
        self.pb_files = files
        self.pb_scale.config(to=len(files) - 1)
        self.show_frame(files.index(current) if current in files else 0)

    def show_frame(self, idx):
        if self.mode != "playback" or not self.pb_files:
            return
        idx = max(0, min(idx, len(self.pb_files) - 1))
        self.pb_index = idx
        path = self.pb_files[idx]
        if path not in self.pb_cache:
            try:
                self.pb_cache[path] = load_csv(path)
            except (OSError, csv.Error, UnicodeDecodeError) as e:
                self.pb_cache[path] = (time_from_filename(path), [])
                self.status.config(text=f"Errore lettura {path.name}: {e}")
        when, nets = self.pb_cache[path]
        self.raw = nets
        self.pb_scale.set(idx)
        self.pb_label.config(text=f"{idx + 1} / {len(self.pb_files)}    {when}")
        self.status.config(text=f"{path.name}  -  {len(nets)} BSSID")
        self.refresh()

    def on_scale(self, value):
        idx = int(float(value))
        if self.mode == "playback" and idx != self.pb_index:
            self.show_frame(idx)

    def step(self, delta):
        if self.mode == "playback":
            self.show_frame(self.pb_index + delta)

    def toggle_play(self):
        if self.pb_after:
            self.stop_play()
            return
        if self.pb_index >= len(self.pb_files) - 1:
            self.show_frame(0)
        self.btn_play.config(text="⏸ Pausa")
        self._play_tick(first=True)

    def _play_tick(self, first=False):
        if not first:
            if self.pb_index >= len(self.pb_files) - 1:
                self.stop_play()
                return
            self.show_frame(self.pb_index + 1)
        try:
            delay = max(0.1, float(self.speed_var.get()))
        except (self.tk.TclError, ValueError):
            delay = 1.0
        self.settings["play_speed"] = delay
        self.pb_after = self.root.after(int(delay * 1000), self._play_tick)

    def stop_play(self):
        if self.pb_after:
            self.root.after_cancel(self.pb_after)
            self.pb_after = None
        self.btn_play.config(text="▶ Play")

    # ---------------------------------------------------------------- chiusura
    def on_close(self):
        for key, var in (("interval", self.interval_var), ("min_rssi", self.thr_var)):
            try:
                self.settings[key] = int(var.get())
            except (self.tk.TclError, ValueError):
                pass
        self.settings["group"] = self.group_var.get()
        self.settings["show_util"] = self.util_var.get()
        self.settings["auto_scan"] = self.auto_var.get()
        store_settings(self.settings)
        if self.scanner is not None and hasattr(self.scanner, "close"):
            self.scanner.close()
        self.root.destroy()

    def run(self):
        self.root.mainloop()


# --------------------------------------------------------------------------
# main
# --------------------------------------------------------------------------

def run_snapshot(nets, path, min_rssi, group, fontsize):
    if group:
        nets = group_radios(nets)
    compute_overlaps(nets, min_rssi)
    fig = Figure(figsize=(16, 11), layout="constrained")
    draw_bands(fig, nets, list(BANDS), min_rssi, fontsize=fontsize)
    fig.savefig(path, dpi=110)
    print(f"{'SSID':<26}{'BSSID':<19}{'Banda':>6}{'Ch':>5}{'MHz':>6}{'Centro':>8}{'dBm':>6}"
          f"  {'Standard':<14}{'Max PHY':>11}  {'Stream':<10}{'Util':>6}{'Sta':>5}  Sovrapposizioni")
    for n in sorted(nets, key=lambda n: (n.primary_freq, -n.rssi)):
        print(f"{n.name[:25]:<26}{n.bssid:<19}{n.band:>6}{n.channel:>5}{n.width:>6}"
              f"{n.center_freq:>8}{n.rssi:>6}  {n.standard:<14}{n.rate_text:>11}  "
              f"{n.stream_text:<10}{n.util_text:>6}{n.stations_text:>5}  {overlap_summary(n)}")
    print(f"\nGrafico salvato in {path}")


def main():
    ap = argparse.ArgumentParser(description="Analizzatore di reti Wi-Fi 2.4 / 5 / 6 GHz")
    ap.add_argument("--demo", action="store_true", help="usa reti simulate")
    ap.add_argument("--interval", type=int, help="secondi tra le scansioni automatiche")
    ap.add_argument("--min-rssi", type=int,
                    help="reti piu' deboli di questa soglia (dBm) non contano come sovrapposizione")
    ap.add_argument("--font-size", type=int, help="dimensione del testo (pt)")
    ap.add_argument("--save-dir", metavar="DIR",
                    help="salva ogni scansione come CSV in DIR (wifi_scan_<data>_<ora>.csv)")
    ap.add_argument("--playback", metavar="DIR", help="riproduce i CSV salvati in DIR")
    ap.add_argument("--no-group", action="store_true",
                    help="non unire gli SSID trasmessi dallo stesso AP (solo --snapshot)")
    ap.add_argument("--snapshot", metavar="FILE.png",
                    help="esegue una scansione, salva il grafico ed esce")
    ap.add_argument("--web", metavar="PORTA", type=int,
                    help="nessuna finestra: espone l'interfaccia via browser su questa porta")
    ap.add_argument("--host", default="127.0.0.1",
                    help="indirizzo su cui ascolta --web (default 127.0.0.1, solo questo PC; "
                         "0.0.0.0 per renderlo raggiungibile dalla rete, protetto da token)")
    ap.add_argument("--token", help="token di accesso per --web (generato se serve e non indicato)")
    args = ap.parse_args()

    settings = load_settings()
    for key, value in (("interval", args.interval), ("min_rssi", args.min_rssi),
                       ("font_size", args.font_size)):
        if value is not None:
            settings[key] = value
    if args.save_dir:
        settings["save_dir"] = str(Path(args.save_dir).resolve())
        settings["save_csv"] = True

    try:
        scanner = make_scanner(args.demo)
    except Exception as e:
        if not args.playback:
            print(f"Impossibile inizializzare lo scanner Wi-Fi: {e}\nProva con --demo.", file=sys.stderr)
            sys.exit(1)
        scanner = None  # il playback funziona anche senza scheda Wi-Fi

    try:
        if args.snapshot:
            nets = scanner.scan()
            if args.save_dir:
                path = save_csv(nets, settings["save_dir"], datetime.now(), settings["min_rssi"])
                print(f"Tabella salvata in {path}")
            run_snapshot(nets, args.snapshot, settings["min_rssi"], not args.no_group,
                         settings["font_size"])
        elif args.web:
            # wifi_web importa "wifi_analyzer": deve trovare questo modulo, non ricaricarlo
            sys.modules.setdefault("wifi_analyzer", sys.modules[__name__])
            import wifi_web
            wifi_web.serve(scanner, settings, args.host, args.web, args.token, args.playback)
        else:
            App(scanner, settings, args.playback).run()
    except PermissionError as e:
        print(e, file=sys.stderr)
        sys.exit(2)
    finally:
        if scanner is not None and hasattr(scanner, "close"):
            scanner.close()


if __name__ == "__main__":
    main()
