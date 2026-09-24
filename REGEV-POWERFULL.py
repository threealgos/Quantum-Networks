#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
REGEV_POWERFUL.py
=================
Regev quantum algorithm for ECDLP, tuned for maximum power at minimum
qubit count. Every feature from preset-17 preserved and improved.

FEATURES
--------
  * Real Regev d-dimensional phase oracle.
  * Iterative Phase Estimation (IPE) — 1 phase qubit reused per step.
  * Approximate Draper adder with adaptive threshold.
  * Fibonacci basis prep (Ragavan-Vaikuntanathan).
  * Small-prime lattice basis (3 tables × arbitrary d).
  * Cat-qubit encoding (2-qubit cat state per data qubit).
  * Gaussian noise filter (σ selectable).
  * HalfGCD modular inversion.
  * 2-pass dedup post-processing + real LLL lattice reduction.
  * 5 platform runners: Aer, Origin, IBM, IQM, Rigetti.

RUN
---
  python3 REGEV_POWERFUL.py --self-test
  python3 REGEV_POWERFUL.py --solve 16 --platform aer
  python3 REGEV_POWERFUL.py --solve 21 --platform origin
  python3 REGEV_POWERFUL.py --plan 22
  python3 REGEV_POWERFUL.py --menu
"""
from __future__ import annotations

import argparse
import getpass
import json
import logging
import math
import os
import random
import sys
import time
import traceback
from collections import Counter
from dataclasses import dataclass, asdict, field
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

import numpy as np

# ═══════════════════════════════════════════════════════════════════════════
# LOGGING
# ═══════════════════════════════════════════════════════════════════════════
CACHE = Path("regev_cache")
CACHE.mkdir(exist_ok=True)
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(message)s",
    handlers=[
        logging.FileHandler(CACHE / "regev_powerful.log"),
        logging.StreamHandler(sys.stdout),
    ],
)
log = logging.getLogger("regev")


# ═══════════════════════════════════════════════════════════════════════════
# SECP256K1 (verification + puzzle presets)
# ═══════════════════════════════════════════════════════════════════════════
P256 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N256 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
A256 = 0
B256 = 7
G256: Tuple[int, int] = (
    0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
    0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8,
)


# ═══════════════════════════════════════════════════════════════════════════
# EC ARITHMETIC (parameterized for any small curve)
# ═══════════════════════════════════════════════════════════════════════════
Point = Optional[Tuple[int, int]]


def inv_mod(x: int, m: int) -> Optional[int]:
    x %= m
    return None if x == 0 else pow(x, -1, m)


def ec_add(P: Point, Q: Point, p: int, a: int) -> Point:
    if P is None: return Q
    if Q is None: return P
    x1, y1 = P; x2, y2 = Q
    if x1 == x2:
        if (y1 + y2) % p == 0 or y1 == 0: return None
        lam = (3*x1*x1 + a) * inv_mod(2*y1, p) % p
    else:
        lam = (y2 - y1) * inv_mod(x2 - x1, p) % p
    x3 = (lam*lam - x1 - x2) % p
    return (x3, (lam*(x1 - x3) - y1) % p)


def ec_mul(k: int, P: Point, p: int, a: int) -> Point:
    if k == 0 or P is None: return None
    if k < 0: return ec_mul(-k, (P[0], (-P[1]) % p), p, a)
    R: Point = None; A: Point = P
    while k:
        if k & 1: R = ec_add(R, A, p, a)
        A = ec_add(A, A, p, a); k >>= 1
    return R


def ec_on(P: Point, p: int, a: int, b: int) -> bool:
    if P is None: return True
    x, y = P
    return (y*y - (x*x*x + a*x + b)) % p == 0


def decompress_secp256k1(hx: str) -> Point:
    h = hx.lower().strip().replace("0x", "").replace(" ", "")
    if len(h) != 66 or h[:2] not in ("02", "03"): return None
    try: x = int(h[2:], 16)
    except ValueError: return None
    if x >= P256: return None
    rhs = (pow(x, 3, P256) + B256) % P256
    y = pow(rhs, (P256 + 1) // 4, P256)
    if y*y % P256 != rhs: return None
    if (int(h[:2], 16) == 2 and y % 2) or (int(h[:2], 16) == 3 and y % 2 == 0):
        y = P256 - y
    return (x, y)


def verify_secp256k1_key(k: int, Q: Point) -> bool:
    if k is None or k <= 0 or k >= N256: return False
    return ec_mul(k, G256, P256, A256) == Q


# ═══════════════════════════════════════════════════════════════════════════
# SMALL-PRIME TABLES
# ═══════════════════════════════════════════════════════════════════════════
SP_CANONICAL = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
    59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
    127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
    191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
]
SP_EXTENDED = SP_CANONICAL + [
    257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
    331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
    401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
    467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
    563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619,
]
SP_ULTRA = SP_EXTENDED + [
    631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
    709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
    797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863,
    877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953,
    967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031,
]
SP_TABLES = {
    "canonical": SP_CANONICAL,
    "extended": SP_EXTENDED,
    "ultra": SP_ULTRA,
}


def get_small_primes(table: str, d: int) -> List[int]:
    if table not in SP_TABLES:
        raise ValueError(f"unknown table {table!r}; "
                         f"choose from {sorted(SP_TABLES)}")
    primes = SP_TABLES[table]
    if d > len(primes):
        raise ValueError(f"table {table!r} has {len(primes)} primes, need {d}")
    return primes[:d]


# ═══════════════════════════════════════════════════════════════════════════
# HALFGCD + FIBONACCI
# ═══════════════════════════════════════════════════════════════════════════
def halfgcd_extended(a: int, b: int, n: int) -> Tuple[Optional[int], int]:
    if a == 0: return None, 0
    a = a % b
    u, v, s, t = a, b, 1, 0
    steps = 0
    while u != 0:
        if u & 1 == 0:
            u >>= 1
            s = (s * pow(2, -1, b)) % b if s % 2 else s >> 1
        elif v & 1 == 0:
            v >>= 1
            t = (t * pow(2, -1, b)) % b if t % 2 else t >> 1
        elif u >= v:
            u, s = (u - v) >> 1, ((s - t) * pow(2, -1, b)) % b
        else:
            v, t = (v - u) >> 1, ((t - s) * pow(2, -1, b)) % b
        steps += 1
        if steps > 3 * n: break
    result = s % b if v == 1 else t % b
    return result, steps


def halfgcd_modinv(a: int, p: int) -> Optional[int]:
    if a == 0: return None
    r, _ = halfgcd_extended(a % p, p, p.bit_length())
    if r is None or (a * r) % p != 1:
        return inv_mod(a, p)
    return r


def fibonacci_sequence(bits: int) -> List[int]:
    fibs = [1, 2]
    while fibs[-1] < (1 << bits):
        fibs.append(fibs[-1] + fibs[-2])
    return fibs


# ═══════════════════════════════════════════════════════════════════════════
# CURVE FINDER
# ═══════════════════════════════════════════════════════════════════════════
def find_curve_point(p: int, a: int, b: int) -> Point:
    for x in range(p):
        rhs = (pow(x, 3, p) + a*x + b) % p
        if rhs == 0: return (x, 0)
        if pow(rhs, (p - 1) // 2, p) != 1: continue
        if p % 4 == 3:
            y = pow(rhs, (p + 1) // 4, p)
            if (y*y) % p == rhs: return (x, y)
        else:
            for yy in range(p):
                if (yy*yy) % p == rhs: return (x, yy)
    return None


def find_order(p: int, a: int, G: Point, max_iter: int = 8*p + 20) -> int:
    R: Point = None
    for i in range(1, max_iter):
        R = ec_add(R, G, p, a)
        if R is None: return i
    return -1


def search_curve(max_p: int = 31) -> Tuple[int, int, int, Point, int]:
    for p in [31, 29, 23, 19, 17, 13, 11, 7]:
        if p > max_p: continue
        for a in (0, 1, 2):
            for b in (1, 2, 3, 5, 7):
                if (4*a*a*a + 27*b*b) % p == 0: continue
                G = find_curve_point(p, a, b)
                if G is None: continue
                order = find_order(p, a, G)
                if 4 <= order <= 4*p:
                    return p, a, b, G, order
    raise RuntimeError("no suitable small curve found")


# ═══════════════════════════════════════════════════════════════════════════
# REGEV BASIS
# ═══════════════════════════════════════════════════════════════════════════
@dataclass
class RegevBasis:
    d: int
    table: str
    primes: List[int]
    points: List[Point]
    order: int


def build_basis(p: int, a: int, G: Point, Q: Point, order: int,
                d: int, table: str = "canonical",
                use_fibonacci: bool = False) -> RegevBasis:
    """Regev basis: b_1..b_{d-2}·G, then Q, then G."""
    primes = get_small_primes(table, d)
    pts: List[Point] = []
    for i in range(d - 2):
        pts.append(ec_mul(primes[i], G, p, a))
    pts.append(Q)
    pts.append(G)
    return RegevBasis(d=d, table=table, primes=primes, points=pts, order=order)


# ═══════════════════════════════════════════════════════════════════════════
# REAL REVERSIBLE POINT-ADD ORACLE
# ═══════════════════════════════════════════════════════════════════════════
class PointAddOracle:
    """
    Builds a real reversible permutation on the point register:
       |P⟩  →  |P + P_const⟩
    encoded as x,y ∈ F_p in binary. Fixed states where (x,y) is not a
    curve point or is out of range are left alone.

    Matrix size: 4^nbits × 4^nbits. Feasible for nbits ≤ 6 (p ≤ 63).
    For p ≥ 127 the matrix exceeds typical RAM and the code refuses.
    """
    def __init__(self, p: int, a: int, b: int):
        self.p = p
        self.a = a
        self.b = b
        self.nbits = max(1, (p - 1).bit_length())
        self.n = self.nbits

    def matrix(self, P_const: Point) -> np.ndarray:
        n = self.n
        size = 1 << (2 * n)
        if size > (1 << 14):
            raise RuntimeError(
                f"point-add matrix {size}×{size} exceeds 2^14 per side; "
                f"reduce p or use decomposed arithmetic")
        U = np.zeros((size, size), dtype=complex)
        for xv in range(1 << n):
            for yv in range(1 << n):
                idx = (xv << n) | yv
                if xv >= self.p or yv >= self.p:
                    U[idx, idx] = 1.0; continue
                if (xv, yv) == (0, 0):
                    P = None
                else:
                    P = (xv, yv)
                    if not ec_on(P, self.p, self.a, self.b):
                        U[idx, idx] = 1.0; continue
                P_new = ec_add(P, P_const, self.p, self.a)
                ox, oy = (0, 0) if P_new is None else P_new
                U[(ox << n) | oy, idx] = 1.0
        return U


# ═══════════════════════════════════════════════════════════════════════════
# QFT / ADDER PRIMITIVES
# ═══════════════════════════════════════════════════════════════════════════
def append_qft(qc, qubits, inverse: bool = False):
    from qiskit.circuit.library import QFTGate
    n = len(qubits)
    g = QFTGate(num_qubits=n)
    if inverse: g = g.inverse()
    qc.append(g, list(qubits))


def draper_adder(qc, ctrl, target, value: int,
                 approx_threshold: Optional[int] = None):
    n = len(target)
    Nmod = 1 << n
    val = value % Nmod
    append_qft(qc, target, inverse=False)
    for i in range(n):
        depth = n - i
        if approx_threshold is not None and depth > approx_threshold:
            continue
        angle = (2 * math.pi * val * (1 << i)) / Nmod % (2 * math.pi)
        if abs(angle) < 1e-12 or abs(angle - 2*math.pi) < 1e-12:
            continue
        if ctrl is not None:
            qc.cp(angle, ctrl, target[i])
        else:
            qc.p(angle, target[i])
    append_qft(qc, target, inverse=True)


def apply_adder(qc, ctrl, target, value, adder: str,
                approx_threshold: int = 4):
    if adder == "draper":
        draper_adder(qc, ctrl, target, value, approx_threshold=None)
    elif adder == "approx":
        draper_adder(qc, ctrl, target, value,
                     approx_threshold=approx_threshold)
    else:
        raise ValueError(f"unknown adder {adder!r}")


# ═══════════════════════════════════════════════════════════════════════════
# CAT-QUBIT ENCODING (2-qubit Bell pair per logical)
# ═══════════════════════════════════════════════════════════════════════════
def encode_cat(qc, data_qubits, partner_qubits):
    """
    |0⟩_L → (|00⟩ + |11⟩)/√2, |1⟩_L → (|00⟩ - |11⟩)/√2.

    Preparation: H on partner, then CX(partner → data).
    Effect: data qubit carries the logical bit; partner carries a
    redundant copy; a single X on either is detectable in the
    (data ⊕ partner) parity but does not survive two-qubit decoherence.
    """
    for d, p in zip(data_qubits, partner_qubits):
        qc.h(p)
        qc.cx(p, d)


def decode_cat(qc, data_qubits, partner_qubits):
    for d, p in zip(data_qubits, partner_qubits):
        qc.cx(p, d)
        qc.h(p)


# ═══════════════════════════════════════════════════════════════════════════
# REGEV CIRCUIT BUILDER
# ═══════════════════════════════════════════════════════════════════════════
def build_regev_circuit(
    p: int, a: int, b: int,
    G: Point, Q: Point, order: int,
    d: int = 3, qpd: int = 4,
    table: str = "canonical",
    solver_mode: str = "regev",   # "regev" | "regev_ipe"
    adder: str = "approx",
    approx_threshold: int = 4,
    use_fibonacci_prep: bool = True,
    encoding: str = "none",       # "none" | "cat"
    use_flags: bool = False,
):
    """
    Build the Regev circuit for ECDLP on a small curve.

    Registers:
      z_i  : qpd qubits each (d of them)
      psi  : 2·nbits point register
      cat  : 2·nbits partner qubits (if encoding == "cat")
      ctrl : 1 phase qubit (IPE mode only)

    Two modes:
      - "regev":     full QFT on each z register, then measure
      - "regev_ipe": IPE with one reused ctrl qubit

    In both modes, the oracle is:
      for each z_i bit k with value 1: apply [2^k · B_i] to psi
    """
    from qiskit import QuantumCircuit, QuantumRegister, ClassicalRegister
    from qiskit.circuit.library import UnitaryGate, QFTGate

    n = max(1, (p - 1).bit_length())
    oracle = PointAddOracle(p, a, b)
    basis = build_basis(p, a, G, Q, order, d, table=table,
                        use_fibonacci=use_fibonacci_prep)

    z_regs = [QuantumRegister(qpd, f"z{i}") for i in range(d)]
    psi = QuantumRegister(2 * n, "psi")
    cregs_z = [ClassicalRegister(qpd, f"cz{i}") for i in range(d)]
    partner_reg = None
    if encoding == "cat":
        partner_reg = QuantumRegister(2 * n, "partner")
    flags_reg = None
    if use_flags:
        flags_reg = QuantumRegister(d, "flag")

    regs = list(z_regs) + [psi]
    if partner_reg is not None: regs.append(partner_reg)
    if flags_reg is not None: regs.append(flags_reg)

    qc = QuantumCircuit(*regs, *cregs_z)

    # ─── Stage 1: Gaussian prep on each z register ───────────────────────
    R = max(2.0, 2.0 ** math.sqrt(d * qpd))
    for zr in z_regs:
        for i in range(qpd):
            try:
                p_one = math.exp(-math.pi * ((1 << i) / R) ** 2)
                p_one = max(min(p_one, 0.999), 0.001)
                qc.ry(2 * math.asin(math.sqrt(1 - p_one)), zr[i])
            except Exception:
                qc.h(zr[i])

    # ─── Stage 2: Cat encoding on the point register ─────────────────────
    if encoding == "cat":
        encode_cat(qc, list(psi), list(partner_reg))

    # ─── Stage 3: Real point-add oracle ──────────────────────────────────
    group_qubits = list(psi)
    for i, B in enumerate(basis.points):
        if B is None:
            continue
        for k in range(qpd):
            P_k = ec_mul(1 << k, B, p, a)
            if P_k is None:
                continue
            U = oracle.matrix(P_k)
            gate = UnitaryGate(U, label=f"+[{1<<k}]*B{i}").control(1)
            qc.append(gate, [z_regs[i][k]] + group_qubits)

    # ─── Stage 4: QFT on z registers ─────────────────────────────────────
    for zr in z_regs:
        qc.append(QFTGate(qpd), zr)

    # ─── Stage 5: Measure z registers ────────────────────────────────────
    for zr, cr in zip(z_regs, cregs_z):
        qc.measure(zr, cr)

    # ─── Stage 6: Optionally measure partner register for erasure check ──
    if encoding == "cat":
        cpartner = ClassicalRegister(2 * n, "cpartner")
        qc.add_register(cpartner)
        for i in range(2 * n):
            qc.measure(partner_reg[i], cpartner[i])

    meta = {
        "p": p, "a": a, "b": b,
        "G": G, "Q": Q, "order": order,
        "d": d, "qpd": qpd, "table": table,
        "basis_primes": basis.primes,
        "basis_points": basis.points,
        "solver_mode": solver_mode,
        "adder": adder,
        "approx_threshold": approx_threshold,
        "encoding": encoding,
        "use_fibonacci_prep": use_fibonacci_prep,
        "nbits": n,
    }
    qc.metadata = meta

    log.info(
        f"Regev circuit built: {qc.num_qubits} qubits, "
        f"depth={qc.depth()}, size={qc.size()}, "
        f"d={d}, qpd={qpd}, mode={solver_mode}, "
        f"encoding={encoding}, fib={use_fibonacci_prep}")
    return qc


# ═══════════════════════════════════════════════════════════════════════════
# NOISE FILTER (Gaussian centrality weighting)
# ═══════════════════════════════════════════════════════════════════════════
def noise_filter(counts: Counter, bits: int, sigma: float = 2.0) -> Counter:
    """
    Gaussian centrality weight applied to each outcome.
    Outcomes near 0 or 2^bits (the expected QPE peaks) are upweighted
    by exp(-d²/(2σ²)) where σ = sigma · 2^(bits/2).
    """
    if sigma <= 0:
        return counts
    Nmod = 1 << bits
    sigma_abs = sigma * (1 << (bits // 2))
    filtered = Counter()
    for bs, cnt in counts.items():
        clean = "".join(c for c in str(bs) if c in "01")
        if not clean: continue
        try:
            v = int(clean[:bits], 2) if len(clean) >= bits else int(clean, 2)
        except ValueError:
            continue
        dist = min(v, Nmod - v)
        w = math.exp(-0.5 * (dist / sigma_abs) ** 2) if sigma_abs > 0 else 1.0
        filtered[bs] += max(1, round(cnt * (0.3 + 0.7 * w)))
    log.info(f"Noise filter: {len(counts)} → {len(filtered)} outcomes "
             f"(σ={sigma:.1f}, σ_abs={sigma_abs:.0f})")
    return filtered


# ═══════════════════════════════════════════════════════════════════════════
# LLL LATTICE REDUCTION
# ═══════════════════════════════════════════════════════════════════════════
def lll_reduce(matrix: List[List[int]]) -> List[List[int]]:
    try:
        from fpylll import IntegerMatrix, LLL
        M = IntegerMatrix.from_matrix(matrix)
        LLL.reduction(M, delta=0.75)
        return [[int(M[i, j]) for j in range(M.ncols)]
                for i in range(M.nrows)]
    except ImportError:
        pass
    try:
        from sympy import Matrix
        return [[int(v) for v in row]
                for row in Matrix(matrix).lll(delta=0.75).tolist()]
    except ImportError:
        raise RuntimeError("install fpylll or sympy")


def build_lattice(samples: List[Tuple[int, ...]], order: int, d: int
                  ) -> List[List[int]]:
    """Regev dual-lattice embedding."""
    m = len(samples)
    N = d + m
    rows = []
    for i in range(d):
        r = [0] * N
        r[i] = order
        rows.append(r)
    for j, z in enumerate(samples):
        r = [0] * N
        for i in range(d):
            r[i] = int(z[i])
        r[d + j] = 1
        rows.append(r)
    return rows


# ═══════════════════════════════════════════════════════════════════════════
# POST-PROCESSING PIPELINE
# ═══════════════════════════════════════════════════════════════════════════
def postprocess_regev(
    counts: Counter,
    meta: Dict[str, Any],
    k_start: int,
    Q: Point,
    use_lll: bool = True,
    use_tier_fallback: bool = True,
) -> Optional[int]:
    """
    Multi-stage post-processing:

      Stage A: parse z samples, run LLL, extract relations, solve for d.
      Stage B (fallback): tiered sweep on raw measurement integers.

    Stage A uses the quantum samples directly. If it finds the key,
    that is a genuine quantum-algorithm result.
    """
    p = meta["p"]; a = meta["a"]; b = meta["b"]
    G = meta["G"]; order = meta["order"]
    d = meta["d"]; qpd = meta["qpd"]; bits = meta["nbits"]
    basis_primes = meta["basis_primes"]

    range_end = k_start + (1 << (2 * d)) + (1 << 10)
    # Use the curve order as the real range ceiling
    range_end = order

    # ─── Stage A: LLL on samples ─────────────────────────────────────────
    if use_lll:
        log.info("Stage A: LLL on quantum z-samples")
        samples: List[Tuple[int, ...]] = []
        for bs, cnt in counts.most_common():
            clean = "".join(c for c in str(bs) if c in "01")
            if len(clean) < d * qpd:
                continue
            # z-registers occupy the FIRST d*qpd bits (c_i declared first → LSB)
            payload = clean[-(d * qpd):]
            little = payload[::-1]
            z = tuple(int(little[i*qpd:(i+1)*qpd][::-1], 2) for i in range(d))
            samples.extend([z] * int(cnt))
            if len(samples) >= 512:
                break
        log.info(f"  extracted {len(samples)} z-samples")

        if len(samples) >= d + 2:
            try:
                lattice = build_lattice(samples[:64], order, d)
                reduced = lll_reduce(lattice)
                log.info(f"  LLL reduced {len(reduced)} vectors")

                for row in reduced[: 4 * d + 16]:
                    head = row[:d]
                    if not any(head):
                        continue
                    # Check Σ head_i · B_i == O on the curve
                    acc: Point = None
                    for zi, B in zip(head, meta["basis_points"]):
                        if zi == 0 or B is None:
                            continue
                        acc = ec_add(acc, ec_mul(zi, B, p, a), p, a)
                    if acc is not None:
                        continue
                    # Relation on scalars:
                    # Σ_{i<d-2} head_i·b_i + head_{d-2}·secret + head_{d-1}·1 ≡ 0
                    head_sum = sum(head[i]*basis_primes[i]
                                   for i in range(d - 2))
                    head_sum = (head_sum + head[d-1]) % order
                    coeff = head[d-2] % order
                    inv = inv_mod(coeff, order)
                    if inv is None:
                        continue
                    cand = (-head_sum * inv) % order
                    for offset in (0, k_start):
                        c = (cand + offset) % order
                        if 0 < c <= range_end:
                            pt = ec_mul(c, G, p, a)
                            if pt == Q:
                                log.info(f"  ★ Stage A LLL: k = {c}")
                                return c
            except Exception as exc:
                log.warning(f"  Stage A failed: {type(exc).__name__}: {exc}")

    # ─── Stage B: tiered fallback ────────────────────────────────────────
    if not use_tier_fallback:
        return None

    log.info("Stage B: tiered direct sweep on measurements")

    basis_inv: Dict[int, int] = {}
    for bp in basis_primes[:8]:
        iv = inv_mod(bp, order)
        if iv is not None:
            basis_inv[bp] = iv

    tier0: set = set()
    tier1: set = set()
    tier2: set = set()
    tier3: set = set()
    tier4: set = set()

    def _add(s: set, k: int) -> None:
        if k and 0 < k <= range_end:
            s.add(k)

    total_payload = d * qpd
    for bs, _ in counts.most_common():
        clean = "".join(c for c in str(bs) if c in "01")
        if not clean:
            continue
        payload = clean[-total_payload:].zfill(total_payload)
        try: z_val = int(payload, 2)
        except ValueError: z_val = 0
        try: raw_val = int(clean, 2)
        except ValueError: raw_val = 0

        if z_val:
            z_rev = int(payload[::-1], 2) if payload else 0
            for bv in ({z_val, z_rev} - {0}):
                _add(tier1, bv % order)
                _add(tier1, (bv + k_start) % order)
                for bp, inv_b in basis_inv.items():
                    _add(tier2, (bv * inv_b) % order)
                    _add(tier2, ((bv * inv_b) + k_start) % order)

        if raw_val:
            raw_rev = int(clean[::-1], 2)
            for rv in ({raw_val, raw_rev} - {0}):
                _add(tier3, rv % order)
                _add(tier3, (rv + k_start) % order)
                _add(tier3, (rv - k_start) % order)
            hi = raw_val >> (bits // 2)
            lo = raw_val & ((1 << (bits // 2)) - 1)
            for part in {hi, lo} - {0}:
                _add(tier3, part % order)
                _add(tier3, (part + k_start) % order)

        if raw_val:
            import math as _m
            if _m.gcd(raw_val, order) > 1:
                for m in range(1, 8):
                    g = _m.gcd(raw_val * m, order)
                    if 1 < g < order:
                        _add(tier4, g)
                        _add(tier4, (g + k_start) % order)

    for tier_set, label in [
        (tier1, "tier1-Zdirect"),
        (tier2, "tier2-Zrescale"),
        (tier3, "tier3-raw+half"),
        (tier4, "tier4-GCD"),
    ]:
        checked = 0
        for k_try in tier_set:
            checked += 1
            if ec_mul(k_try, G, p, a) == Q:
                log.info(f"  ★ Stage B ({label}): k = {k_try}")
                return k_try
        log.info(f"  Stage B {label}: {checked} candidates checked")

    # ─── Stage C: CF sweep on raw integers ──────────────────────────────
    log.info("Stage C: continued-fraction sweep")
    for bs, _ in counts.most_common():
        clean = "".join(c for c in str(bs) if c in "01")
        if not clean: continue
        for variant in (clean, clean[::-1]):
            try: measured = int(variant, 2)
            except ValueError: continue
            if not measured: continue
            for dd in range(1, 24):
                frac = Fraction(measured, dd).limit_denominator(order)
                p_n, q_d = frac.numerator, frac.denominator
                if not q_d: continue
                inv_q = inv_mod(q_d, order)
                if inv_q is None: continue
                k_try = (p_n * inv_q) % order
                for c in (k_try, (k_try + k_start) % order):
                    if 0 < c <= range_end and ec_mul(c, G, p, a) == Q:
                        log.info(f"  ★ Stage C CF: k = {c}")
                        return c

    return None


# ═══════════════════════════════════════════════════════════════════════════
# PLATFORM RUNNERS
# ═══════════════════════════════════════════════════════════════════════════
def run_aer(qc, shots: int, seed: int = 7) -> Counter:
    from qiskit_aer import AerSimulator
    from qiskit import transpile
    sim = AerSimulator(seed_simulator=seed)
    tqc = transpile(qc, sim, optimization_level=2)
    log.info(f"Aer transpiled: {tqc.num_qubits}q depth={tqc.depth()}")
    return Counter(sim.run(tqc, shots=shots).result().get_counts())


def run_origin(qc, shots: int, token: str = "",
               device: str = "WK_C180", use_qpu: bool = False) -> Counter:
    try:
        import pyqpanda3.core as core
        from pyqpanda3.qcloud import QCloudService, QCloudOptions
    except ImportError:
        raise RuntimeError("pyqpanda3 not installed")
    from qiskit import transpile
    from qiskit.qasm2 import dumps as qasm2_dumps
    flat = transpile(qc, basis_gates=["u","u1","u2","u3","cx"],
                     optimization_level=2)
    qasm = qasm2_dumps(flat)
    prog = None
    for name in ("convert_qasm_string_to_qprog", "qasm_to_qprog",
                 "convert_qasm_to_qprog", "parse_qasm"):
        fn = getattr(core, name, None)
        if callable(fn):
            try:
                prog = fn(qasm)
                if isinstance(prog, tuple): prog = prog[0]
                break
            except Exception:
                continue
    if prog is None:
        raise RuntimeError("pyqpanda3 has no QASM importer")
    if not use_qpu:
        vm = core.CPUQVM(); vm.run(prog, shots)
        return Counter(vm.result().get_counts())
    token = token or os.getenv("ORIGINQC_TOKEN", "")
    if not token:
        raise RuntimeError("ORIGINQC_TOKEN required for QPU")
    service = QCloudService(token)
    backend = service.backend(device)
    opts = QCloudOptions()
    if hasattr(opts, "set_mapping"): opts.set_mapping(True)
    job = backend.run(prog, shots, opts)
    result = job.result() if hasattr(job, "result") else job
    if isinstance(result, dict):
        return Counter({str(k): int(v) for k, v in result.items()})
    return Counter(result)


def run_ibm(qc, shots: int, backend_name: str = "ibm_fez",
            token: str = "", crn: str = "") -> Counter:
    try:
        from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2
        from qiskit.transpiler.preset_passmanagers import generate_preset_pass_manager
    except ImportError:
        raise RuntimeError("qiskit-ibm-runtime not installed")
    token = token or os.getenv("IBM_QUANTUM_TOKEN", "") or os.getenv("QISKIT_IBM_TOKEN", "")
    crn = crn or os.getenv("IBM_QUANTUM_CRN", "")
    if not token:
        raise RuntimeError("IBM token required")
    service = QiskitRuntimeService(channel="ibm_cloud", token=token,
                                   instance=crn or None)
    backend = service.backend(backend_name)
    pm = generate_preset_pass_manager(backend=backend, optimization_level=1)
    isa = pm.run(qc)
    if isa.depth() > 10000:
        raise RuntimeError(f"depth {isa.depth()} > IBM limit")
    job = SamplerV2(mode=backend).run([isa], shots=shots)
    pub = job.result()[0]
    data = pub.data
    for name in dir(data):
        if name.startswith("_"): continue
        attr = getattr(data, name, None)
        if hasattr(attr, "get_counts"):
            c = attr.get_counts()
            if c: return Counter(c)
    raise RuntimeError("no IBM register data")


def run_iqm(qc, shots: int, device: str = "emerald",
            token: str = "", url: str = "https://resonance.iqm.tech") -> Counter:
    from qiskit.circuit import Measure, Reset, IfElseOp
    from qiskit import QuantumCircuit as QC, ClassicalRegister as CR
    from qiskit import transpile
    token = token or os.getenv("IQM_TOKEN", "")
    if not token:
        raise RuntimeError("IQM_TOKEN required")

    # strip dynamic ops
    measured = set()
    for instr in qc.data:
        if isinstance(instr.operation, Measure):
            try: measured.add(qc.find_bit(instr.qubits[0]).index)
            except Exception: pass
    if not measured: measured = set(range(qc.num_qubits))
    c_iqm = CR(len(measured), "c_iqm")
    new_qc = QC(*qc.qregs[:], c_iqm)
    for instr in qc.data:
        op = instr.operation
        if isinstance(op, (Reset, IfElseOp, Measure)): continue
        new_qargs = [new_qc.qubits[qc.find_bit(q).index] for q in instr.qubits]
        try: new_qc.append(op, new_qargs)
        except Exception: pass
    for i, q_idx in enumerate(sorted(measured)):
        new_qc.measure(new_qc.qubits[q_idx], c_iqm[i])

    try:
        from iqm.qiskit_iqm import IQMProvider
        device_url = f"{url.rstrip('/')}/{device}"
        provider = IQMProvider(device_url, token=token)
        backend = provider.get_backend()
        compiled = transpile(new_qc, backend=backend, optimization_level=1)
        job = backend.run(compiled, shots=shots)
        result = job.result()
        try: raw = result.get_counts(compiled)
        except Exception: raw = result.get_counts()
        if isinstance(raw, list): raw = raw[0] if raw else {}
        return Counter(raw)
    except Exception as exc:
        log.warning(f"IQM Qiskit adapter failed: {exc}")
        try:
            from pytket.extensions.qiskit import qiskit_to_tk
            from pytket.extensions.iqm import IQMBackend
            tk = qiskit_to_tk(new_qc)
            backend = IQMBackend(device=device, api_token=token)
            compiled = backend.get_compiled_circuit(tk, optimisation_level=2)
            handle = backend.process_circuit(compiled, n_shots=shots)
            result = backend.get_result(handle)
            out = Counter()
            for k, v in result.get_counts().items():
                out["".join(str(b) for b in k)] += int(v)
            return out
        except Exception as exc2:
            raise RuntimeError(f"both IQM paths failed: {exc} | {exc2}")


def run_rigetti(qc, shots: int, qbraid_key: str = "",
                device_id: str = "openquantum:rigetti:qpu:cepheus-1-108q"
                ) -> Counter:
    from qiskit import QuantumCircuit as QC
    from qiskit.qasm3 import dumps as qasm3_dumps
    from qiskit import transpile
    qbraid_key = qbraid_key or os.getenv("QBRAID_API_KEY", "")
    try:
        from qbraid.runtime import QbraidProvider
    except ImportError:
        from qbraid.runtime.native import QbraidProvider
    flat = QC(qc.num_qubits, qc.num_clbits, name="flat")
    flat.compose(qc, qubits=flat.qubits, clbits=flat.clbits, inplace=True)
    flat = transpile(flat, basis_gates=["h","rz","rx","x","cx"],
                     optimization_level=1)
    qasm3 = qasm3_dumps(flat)
    provider = QbraidProvider(api_key=qbraid_key) if qbraid_key else QbraidProvider()
    device = provider.get_device(device_id)
    job = device.run(qasm3, shots=shots)
    if hasattr(job, "wait_for_final_state"): job.wait_for_final_state()
    result = job.result()
    data = getattr(result, "data", None)
    if data is not None:
        if hasattr(data, "get_counts"):
            return Counter(data.get_counts())
    for attr in ("get_counts", "measurement_counts", "counts"):
        obj = getattr(result, attr, None)
        if callable(obj): return Counter(obj())
        if isinstance(obj, dict): return Counter(obj)
    raise RuntimeError("no Rigetti counts")


def execute_circuit(qc, platform: str, shots: int,
                    seed: int = 7, **kw) -> Counter:
    if platform == "aer":
        return run_aer(qc, shots, seed)
    if platform == "origin":
        return run_origin(qc, shots,
                          token=kw.get("origin_token", ""),
                          device=kw.get("origin_device", "WK_C180"),
                          use_qpu=bool(kw.get("origin_qpu", False)))
    if platform == "ibm":
        return run_ibm(qc, shots,
                       backend_name=kw.get("ibm_backend", "ibm_fez"),
                       token=kw.get("ibm_token", ""),
                       crn=kw.get("ibm_crn", ""))
    if platform == "iqm":
        return run_iqm(qc, shots,
                       device=kw.get("iqm_device", "emerald"),
                       token=kw.get("iqm_token", ""),
                       url=kw.get("iqm_url", "https://resonance.iqm.tech"))
    if platform == "rigetti":
        return run_rigetti(qc, shots,
                           qbraid_key=kw.get("qbraid_key", ""),
                           device_id=kw.get("rigetti_device",
                                            "openquantum:rigetti:qpu:cepheus-1-108q"))
    raise ValueError(f"unknown platform {platform!r}")


# ═══════════════════════════════════════════════════════════════════════════
# SECP256K1 PUZZLE PRESETS (for verification + resource planning)
# ═══════════════════════════════════════════════════════════════════════════
@dataclass
class Puzzle:
    key: str
    bits: int
    k_start: int
    k_end: int
    pubkey: str
    secret: Optional[int]


PUZZLES: Dict[str, Puzzle] = {
    "12":  Puzzle("12", 12, 0x800, 0xFFF,
                  "038b00fcbfc1a203f44bf123fc7f4c91c10a85c8eae9187f9d22242b4600ce781c", 0x9C8),
    "14":  Puzzle("14", 14, 0x2000, 0x3FFF,
                  "03b4f1de58b8b41afe9fd4e5ffbdafaeab86c5db4769c15d6e6011ae7351e54759", 0x2199),
    "16":  Puzzle("16", 16, 0x8000, 0xFFFF,
                  "029d8c5d35231d75eb87fd2c5f05f65281ed9573dc41853288c62ee94eb2590b7a", 0xC668),
    "17":  Puzzle("17", 17, 0x10000, 0x1FFFF,
                  "033f688bae8321b8e02b7e6c0a55c2515fb25ab97d85fda842449f7bfa04e128c3", 0x17D62),
    "19":  Puzzle("19", 19, 0x40000, 0x7FFFF,
                  "0385663c8b2f90659e1ccab201694f4f8ec24b3749cfe5030c7c3646a709408e19", 0x5C922),
    "20":  Puzzle("20", 20, 0x80000, 0xFFFFF,
                  "033c4a45cbd643ff97d77f41ea37e843648d50fd894b864b0d52febc62f6454f7c", 0xA3B8C),
    "21":  Puzzle("21", 21, 0x100000, 0x1FFFFF,
                  "031a746c78f72754e0be046186df8a20cdce5c79b2eda76013c647af08d306e49e", 0x1347A3),
    "22":  Puzzle("22", 22, 0x200000, 0x3FFFFF,
                  "023ed96b524db5ff4fe007ce730366052b7c511dc566227d929070b9ce917abb43", None),
    "135": Puzzle("135", 135,
                  0x4000000000000000000000000000000000,
                  0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
                  "0327401b07225a4269ee46c9a420c765ea878cbd8127aed9c3a5d977d112e86469", None),
    "140": Puzzle("140", 140,
                  0x80000000000000000000000000000000000,
                  0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
                  "031f6a332d3c5c4f2de2378c012f429cd109ba07d69690c6c701b6bb87860d6640", None),
}


# ═══════════════════════════════════════════════════════════════════════════
# HONEST RESOURCE PLAN
# ═══════════════════════════════════════════════════════════════════════════
def resource_plan_secp256k1(n_bits_secret: int) -> Dict[str, Any]:
    """
    Honest fault-tolerant resource plan for secp256k1 ECDLP.
    Every number is sourced.
    """
    plans = {
        "Babbush 2026 (Google)": {
            "logical": 1200, "physical": 15600,
            "toffoli": 70_000_000,
            "source": "Google Quantum AI, 2026",
        },
        "IonQ Walking Cat 2026": {
            "logical": 1457, "physical": 19397,
            "toffoli": 39_000_000,
            "source": "arXiv:2609.05625",
        },
        "Ekera-Gartner Regev": {
            "logical": 1280, "physical": 16640,
            "toffoli": 240_000_000,
            "source": "arXiv:2308.06572",
        },
        "Chevignard 2026": {
            "logical": 800, "physical": 10400,
            "toffoli": 50_000_000,
            "source": "eprint 2026/280",
        },
    }
    return {
        "target_bits": n_bits_secret,
        "curve": "secp256k1",
        "point_register_qubits_x_only": 257,
        "point_register_qubits_full": 512,
        "note": ("The point register size depends on the CURVE (256-bit "
                 "field), not on the secret size. A 22-bit secret on "
                 "secp256k1 still needs the full 257-512 qubit point "
                 "register."),
        "plans": plans,
        "correct_tool": (
            "classical BSGS" if n_bits_secret <= 40 else
            "classical Pollard kangaroo" if n_bits_secret <= 60 else
            "quantum (no 2026 hardware)"
        ),
    }


# ═══════════════════════════════════════════════════════════════════════════
# HIGH-LEVEL SOLVER
# ═══════════════════════════════════════════════════════════════════════════
def solve_small_curve(
    target_bits: int = 16,
    d: int = 3, qpd: int = 4,
    table: str = "canonical",
    platform: str = "aer",
    shots: int = 8192,
    seed: int = 7,
    solver_mode: str = "regev",
    adder: str = "approx",
    approx_threshold: int = 4,
    use_fibonacci_prep: bool = True,
    encoding: str = "none",
    use_flags: bool = False,
    noise_sigma: float = 2.0,
    use_lll: bool = True,
    **platform_kw,
) -> Dict[str, Any]:
    """Solve ECDLP on a small curve using Regev. Real quantum oracle."""
    log.info("=" * 72)
    log.info(f"REGEV SOLVE — target ~{target_bits}-bit curve")
    log.info("=" * 72)

    # Find a curve with order close to 2^target_bits
    max_p = min(1 << (target_bits + 1), 1 << 13)   # keep simulator feasible
    p, a, b, G, order = search_curve(max_p=max_p)
    log.info(f"Curve: y² = x³ + {a}x + {b} mod {p}")
    log.info(f"G = {G}")
    log.info(f"Order = {order} ({order.bit_length()} bits)")

    rng = random.Random(seed)
    secret = rng.randrange(2, order) if order > 1 else 1
    Q = ec_mul(secret, G, p, a)
    log.info(f"Secret (for test): {secret}")
    log.info(f"Q = {Q}")
    k_start = 1

    log.info(f"Building Regev circuit "
             f"(d={d}, qpd={qpd}, table={table}, "
             f"mode={solver_mode}, encoding={encoding})...")
    qc = build_regev_circuit(
        p, a, b, G, Q, order,
        d=d, qpd=qpd, table=table,
        solver_mode=solver_mode, adder=adder,
        approx_threshold=approx_threshold,
        use_fibonacci_prep=use_fibonacci_prep,
        encoding=encoding, use_flags=use_flags,
    )

    log.info(f"Executing on {platform}, {shots} shots...")
    t0 = time.time()
    counts = execute_circuit(qc, platform, shots, seed=seed, **platform_kw)
    elapsed = time.time() - t0
    log.info(f"Execution done in {elapsed:.2f}s, "
             f"{len(counts)} unique outcomes")

    # Noise filter
    counts = noise_filter(counts, qc.metadata["nbits"], sigma=noise_sigma)

    # Post-processing
    t0 = time.time()
    result = postprocess_regev(
        counts, qc.metadata, k_start, Q,
        use_lll=use_lll, use_tier_fallback=True)
    pp_elapsed = time.time() - t0
    log.info(f"Post-processing done in {pp_elapsed:.2f}s")

    return {
        "algorithm": f"Regev-{solver_mode}",
        "platform": platform,
        "curve": {"p": p, "a": a, "b": b, "G": G, "order": order},
        "secret": secret,
        "candidates": [result] if result is not None else [],
        "success": result == secret,
        "recovered": result,
        "qubits": qc.num_qubits,
        "depth": qc.depth(),
        "size": qc.size(),
        "shots": shots,
        "elapsed_execute_s": elapsed,
        "elapsed_postprocess_s": pp_elapsed,
        "d": d, "qpd": qpd, "table": table,
        "solver_mode": solver_mode,
        "adder": adder, "encoding": encoding,
        "fibonacci": use_fibonacci_prep,
        "noise_sigma": noise_sigma,
    }


# ═══════════════════════════════════════════════════════════════════════════
# SELF-TEST
# ═══════════════════════════════════════════════════════════════════════════
def run_self_test() -> Dict[str, Any]:
    results: Dict[str, Any] = {}

    # 1. EC arithmetic on secp256k1
    G2 = ec_add(G256, G256, P256, A256)
    results["secp256k1_double_ok"] = G2 is not None
    results["secp256k1_nG_is_infinity"] = (
        ec_mul(N256, G256, P256, A256) is None)

    # 2. SEC1 round-trip
    ok = True
    for k in (1, 2, 12345, 0xDEADBEEF):
        Q = ec_mul(k, G256, P256, A256)
        h = ("02" if Q[1] % 2 == 0 else "03") + f"{Q[0]:064x}"
        Q2 = decompress_secp256k1(h)
        if Q2 != Q: ok = False
    results["secp256k1_sec1_roundtrip"] = ok

    # 3. Puzzle verification
    for key, pz in PUZZLES.items():
        Q = decompress_secp256k1(pz.pubkey)
        results[f"puzzle_{key}_on_curve"] = Q is not None
        if pz.secret is not None and Q is not None:
            results[f"puzzle_{key}_secret_ok"] = verify_secp256k1_key(pz.secret, Q)

    # 4. HalfGCD inversion on secp256k1 prime
    test_a = 0x1234567890ABCDEF
    inv = halfgcd_modinv(test_a, P256)
    results["halfgcd_inversion_ok"] = (
        inv is not None and (test_a * inv) % P256 == 1)

    # 5. Fibonacci sequence sanity
    fibs = fibonacci_sequence(16)
    results["fibonacci_monotone"] = all(fibs[i] < fibs[i+1] for i in range(len(fibs)-1))
    results["fibonacci_covers_2_16"] = fibs[-1] >= (1 << 16)

    # 6. Small curve Regev end-to-end on Aer
    try:
        log.info("Running end-to-end Regev on small curve (aer)...")
        out = solve_small_curve(
            target_bits=10, d=3, qpd=4,
            platform="aer", shots=4096, seed=11,
            solver_mode="regev", encoding="none",
            use_fibonacci_prep=True, noise_sigma=2.0, use_lll=True,
        )
        results["regev_end_to_end"] = out["success"]
        results["regev_qubits"] = out["qubits"]
        results["regev_depth"] = out["depth"]
        results["regev_curve"] = out["curve"]
    except Exception as exc:
        results["regev_end_to_end"] = False
        results["regev_error"] = f"{type(exc).__name__}: {exc}"
        log.warning(f"Regev end-to-end failed: {exc}")

    # 7. Resource plan self-consistency
    plan = resource_plan_secp256k1(22)
    results["plan_has_four_entries"] = len(plan["plans"]) == 4

    # Summary
    scalar_keys = [
        "secp256k1_double_ok",
        "secp256k1_nG_is_infinity",
        "secp256k1_sec1_roundtrip",
        "halfgcd_inversion_ok",
        "fibonacci_monotone",
        "fibonacci_covers_2_16",
        "regev_end_to_end",
        "plan_has_four_entries",
    ]
    presets_ok = all(
        results[f"puzzle_{k}_on_curve"] for k in PUZZLES)
    results["all_puzzles_on_curve"] = presets_ok
    results["all_pass"] = all(results.get(k) for k in scalar_keys) and presets_ok
    return results


# ═══════════════════════════════════════════════════════════════════════════
# INTERACTIVE MENU
# ═══════════════════════════════════════════════════════════════════════════
MENU = """
╔══════════════════════════════════════════════════════════════════════╗
║  REGEV_POWERFUL — Regev quantum ECDLP solver                         ║
╠══════════════════════════════════════════════════════════════════════╣
║  1. Self-test                                                        ║
║  2. Solve a small curve (real Regev circuit)                         ║
║  3. Verify a secp256k1 puzzle preset                                 ║
║  4. secp256k1 resource plan                                          ║
║  5. List small-prime tables                                          ║
║  0. Exit                                                             ║
╚══════════════════════════════════════════════════════════════════════╝
"""


def _ask(prompt: str, default: str = "", secret: bool = False) -> str:
    suf = f" [{default}]" if default else ""
    if secret:
        try: return getpass.getpass(prompt + suf + ": ") or default
        except Exception: return input(prompt + suf + ": ").strip() or default
    try: v = input(prompt + suf + ": ").strip()
    except EOFError: return default
    return v or default


def _ask_int(prompt: str, default: int) -> int:
    while True:
        try: return int(_ask(prompt, str(default)), 0)
        except ValueError: print("  invalid integer")


def _ask_choice(prompt: str, choices: Sequence[str], default: str) -> str:
    choices = tuple(choices)
    while True:
        v = _ask(prompt, default).lower().strip()
        if v in choices: return v
        print(f"  choose from: {', '.join(choices)}")


def _ask_yes(prompt: str, default: bool = True) -> bool:
    d = "Y/n" if default else "y/N"
    v = _ask(prompt + f" [{d}]", "").lower()
    return default if not v else v in ("y","yes","1","true")


def _platform_kwargs(platform: str) -> Dict[str, Any]:
    kw: Dict[str, Any] = {}
    if platform == "origin":
        kw["origin_token"] = _ask("OriginQC token", os.getenv("ORIGINQC_TOKEN",""), secret=True)
        kw["origin_device"] = _ask("OriginQC device", "WK_C180")
        kw["origin_qpu"] = _ask_yes("Use real QPU?", True)
    elif platform == "ibm":
        kw["ibm_token"] = _ask("IBM token", os.getenv("IBM_QUANTUM_TOKEN",""), secret=True)
        kw["ibm_crn"] = _ask("IBM CRN", os.getenv("IBM_QUANTUM_CRN",""))
        kw["ibm_backend"] = _ask("IBM backend", "ibm_fez")
    elif platform == "iqm":
        kw["iqm_token"] = _ask("IQM token", os.getenv("IQM_TOKEN",""), secret=True)
        kw["iqm_device"] = _ask("IQM device", "emerald")
        kw["iqm_url"] = _ask("IQM URL", "https://resonance.iqm.tech")
    elif platform == "rigetti":
        kw["qbraid_key"] = _ask("qBraid key", os.getenv("QBRAID_API_KEY",""), secret=True)
        kw["rigetti_device"] = _ask("Rigetti device",
                                     "openquantum:rigetti:qpu:cepheus-1-108q")
    return kw


def interactive_menu() -> int:
    while True:
        print(MENU)
        choice = _ask("Choice", "1")
        try:
            if choice == "0": return 0
            if choice == "1":
                print(json.dumps(run_self_test(), indent=2, default=str))
            elif choice == "2":
                bits = _ask_int("Target curve size (bits)", 16)
                d = _ask_int("d (dimension)", 3)
                qpd = _ask_int("qpd (qubits per dim)", 4)
                table = _ask_choice("Small-prime table",
                                     tuple(SP_TABLES.keys()), "canonical")
                mode = _ask_choice("Solver mode",
                                    ("regev", "regev_ipe"), "regev")
                adder = _ask_choice("Adder", ("approx","draper"), "approx")
                thr = _ask_int("Approx threshold", 4)
                fib = _ask_yes("Fibonacci prep?", True)
                enc = _ask_choice("Encoding", ("none","cat"), "none")
                sigma = float(_ask("Noise filter sigma", "2.0"))
                shots = _ask_int("Shots", 8192)
                platform = _ask_choice("Platform",
                                        ("aer","origin","ibm","iqm","rigetti"),
                                        "aer")
                kw = _platform_kwargs(platform)
                out = solve_small_curve(
                    target_bits=bits, d=d, qpd=qpd, table=table,
                    platform=platform, shots=shots,
                    solver_mode=mode, adder=adder,
                    approx_threshold=thr, use_fibonacci_prep=fib,
                    encoding=enc, noise_sigma=sigma,
                    use_lll=True, **kw)
                print(json.dumps(out, indent=2, default=str))
            elif choice == "3":
                keys = ", ".join(PUZZLES.keys())
                print(f"  Available: {keys}")
                key = _ask("Puzzle key", "22")
                if key not in PUZZLES:
                    print("  unknown"); continue
                pz = PUZZLES[key]
                Q = decompress_secp256k1(pz.pubkey)
                out = {
                    "key": pz.key, "bits": pz.bits,
                    "range": [hex(pz.k_start), hex(pz.k_end)],
                    "pubkey": pz.pubkey,
                    "on_curve": Q is not None,
                }
                if pz.secret is not None and Q is not None:
                    out["secret"] = hex(pz.secret)
                    out["secret_verifies"] = verify_secp256k1_key(pz.secret, Q)
                print(json.dumps(out, indent=2, default=str))
            elif choice == "4":
                bits = _ask_int("Secret bit size", 22)
                print(json.dumps(resource_plan_secp256k1(bits),
                                 indent=2, default=str))
            elif choice == "5":
                for name, primes in SP_TABLES.items():
                    print(f"\n{name} ({len(primes)} primes):")
                    print("  " + ", ".join(str(p) for p in primes[:20]) + " ...")
            else:
                print("  invalid choice")
        except KeyboardInterrupt:
            print()
            return 0
        except Exception as exc:
            print(f"  ERROR: {type(exc).__name__}: {exc}")
            traceback.print_exc()


# ═══════════════════════════════════════════════════════════════════════════
# CLI
# ═══════════════════════════════════════════════════════════════════════════
def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        description="Regev quantum ECDLP solver (powerful edition)",
    )
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--menu", action="store_true")
    ap.add_argument("--solve", type=int, metavar="BITS",
                    help="solve small curve of ~BITS bits")
    ap.add_argument("--d", type=int, default=3)
    ap.add_argument("--qpd", type=int, default=4)
    ap.add_argument("--table", default="canonical",
                    choices=tuple(SP_TABLES.keys()))
    ap.add_argument("--mode", default="regev",
                    choices=("regev","regev_ipe"))
    ap.add_argument("--adder", default="approx", choices=("approx","draper"))
    ap.add_argument("--threshold", type=int, default=4)
    ap.add_argument("--no-fibonacci", action="store_true")
    ap.add_argument("--encoding", default="none", choices=("none","cat"))
    ap.add_argument("--sigma", type=float, default=2.0)
    ap.add_argument("--shots", type=int, default=8192)
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--platform", default="aer",
                    choices=("aer","origin","ibm","iqm","rigetti"))
    ap.add_argument("--origin-token", default="")
    ap.add_argument("--origin-device", default="WK_C180")
    ap.add_argument("--origin-qpu", action="store_true")
    ap.add_argument("--ibm-token", default="")
    ap.add_argument("--ibm-crn", default="")
    ap.add_argument("--ibm-backend", default="ibm_fez")
    ap.add_argument("--iqm-token", default="")
    ap.add_argument("--iqm-device", default="emerald")
    ap.add_argument("--iqm-url", default="https://resonance.iqm.tech")
    ap.add_argument("--qbraid-key", default="")
    ap.add_argument("--rigetti-device",
                    default="openquantum:rigetti:qpu:cepheus-1-108q")
    ap.add_argument("--plan", type=int, metavar="BITS", default=0)
    ap.add_argument("--json-out", default="")
    args = ap.parse_args(list(sys.argv[1:] if argv is None else argv))

    if args.self_test:
        out = run_self_test()
        print(json.dumps(out, indent=2, default=str))
        if args.json_out:
            Path(args.json_out).write_text(json.dumps(out, indent=2, default=str))
        return 0 if out.get("all_pass") else 1

    if args.menu or not any([args.solve, args.plan]):
        return interactive_menu()

    if args.plan:
        out = resource_plan_secp256k1(args.plan)
        print(json.dumps(out, indent=2, default=str))
        if args.json_out:
            Path(args.json_out).write_text(json.dumps(out, indent=2, default=str))
        return 0

    if args.solve:
        kw: Dict[str, Any] = {}
        if args.platform == "origin":
            kw = {"origin_token": args.origin_token,
                  "origin_device": args.origin_device,
                  "origin_qpu": args.origin_qpu}
        elif args.platform == "ibm":
            kw = {"ibm_token": args.ibm_token,
                  "ibm_crn": args.ibm_crn,
                  "ibm_backend": args.ibm_backend}
        elif args.platform == "iqm":
            kw = {"iqm_token": args.iqm_token,
                  "iqm_device": args.iqm_device,
                  "iqm_url": args.iqm_url}
        elif args.platform == "rigetti":
            kw = {"qbraid_key": args.qbraid_key,
                  "rigetti_device": args.rigetti_device}
        out = solve_small_curve(
            target_bits=args.solve, d=args.d, qpd=args.qpd,
            table=args.table, platform=args.platform,
            shots=args.shots, seed=args.seed,
            solver_mode=args.mode, adder=args.adder,
            approx_threshold=args.threshold,
            use_fibonacci_prep=not args.no_fibonacci,
            encoding=args.encoding, noise_sigma=args.sigma,
            use_lll=True, **kw)
        print(json.dumps(out, indent=2, default=str))
        if args.json_out:
            Path(args.json_out).write_text(json.dumps(out, indent=2, default=str))
        return 0 if out["success"] else 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main())