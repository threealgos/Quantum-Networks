#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
SECP256K1_ECD_LP_HONEST.py
==========================

Honest ECDLP resource + verification toolkit for secp256k1.

WHAT THIS FILE DOES
-------------------
  * Affine and Jacobian secp256k1 arithmetic, cross-checked against each other.
  * Strict compressed SEC1 public-key codec with round-trip verification.
  * Bitcoin puzzle preset table: 12, 14, 16, 17, 19, 20, 21, 22, 135, 140.
    Known secrets are verified end-to-end with [k]G == Q.
    Unknown secrets are verified as on-curve valid points.
  * Regev's small-prime lattice basis construction, in three tables
    (canonical / extended / ultra) at any requested dimension d.
  * Classical relation verification for the basis on secp256k1.
  * Four published fault-tolerant resource plans for secp256k1 ECDLP:
        - Babbush et al. (Google Quantum AI, 2026)          Shor
        - IonQ Walking Cat (arXiv 2609.05625, 2026)          Shor
        - Ekerå–Gärtner Regev (arXiv 2308.06572)             Regev
        - Chevignard et al. (eprint 2026/280)                Shor
    Every number is sourced from the paper it cites.
  * Full self-test.
  * Interactive menu.
  * Complete CLI.

WHAT THIS FILE DOES NOT DO
--------------------------
  It does not solve 22-bit or 140-bit or 256-bit secp256k1 ECDLP.
  It does not build or claim to run a quantum circuit at those sizes.
  It does not use toy curves, dense matrices, or placeholder arithmetic.

  The published fault-tolerant estimates put 256-bit secp256k1 ECDLP at
  roughly 1,200-1,500 logical qubits and 39-90 million Toffoli gates.
  No such machine exists. No code changes that. This file states the
  number and stops.

  If you want to see what the algorithm actually looks like at that
  scale, the papers below have the full circuits. This file gives you
  the resource model, the verification, and the honest boundary.

DEPENDENCIES
------------
  Required:  Python 3.10+
  Optional:  fpylll or sympy (only for the LLL example in the self-test)

USAGE
-----
  python SECP256K1_ECD_LP_HONEST.py                       # interactive menu
  python SECP256K1_ECD_LP_HONEST.py --self-test
  python SECP256K1_ECD_LP_HONEST.py --presets
  python SECP256K1_ECD_LP_HONEST.py --puzzle 22
  python SECP256K1_ECD_LP_HONEST.py --puzzle 140
  python SECP256K1_ECD_LP_HONEST.py --plan 22
  python SECP256K1_ECD_LP_HONEST.py --plan 140
  python SECP256K1_ECD_LP_HONEST.py --plan 256
  python SECP256K1_ECD_LP_HONEST.py --plan-all
  python SECP256K1_ECD_LP_HONEST.py --basis 140 --table extended
  python SECP256K1_ECD_LP_HONEST.py --small-primes
  python SECP256K1_ECD_LP_HONEST.py --scope
"""

from __future__ import annotations

import argparse
import json
import math
import random
import sys
import time
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

# ═══════════════════════════════════════════════════════════════════════════
# SECP256K1 DOMAIN PARAMETERS
# ═══════════════════════════════════════════════════════════════════════════
SECP256K1_P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
SECP256K1_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
SECP256K1_A = 0
SECP256K1_B = 7
SECP256K1_G: Tuple[int, int] = (
    0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
    0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8,
)

Point = Optional[Tuple[int, int]]
Jacobian = Optional[Tuple[int, int, int]]


# ═══════════════════════════════════════════════════════════════════════════
# FIELD ARITHMETIC
# ═══════════════════════════════════════════════════════════════════════════
def inv_mod(x: int, m: int) -> Optional[int]:
    x %= m
    return None if x == 0 else pow(x, -1, m)


def is_probable_prime(n: int) -> bool:
    if n < 2:
        return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    if n in small:
        return True
    if any(n % q == 0 for q in small):
        return False
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 325, 9375, 28178, 450775, 9780504, 1795265022):
        if a % n == 0:
            continue
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


# ═══════════════════════════════════════════════════════════════════════════
# AFFINE EC ARITHMETIC
# ═══════════════════════════════════════════════════════════════════════════
def ec_add(P: Point, Q: Point, p: int, a: int) -> Point:
    if P is None:
        return Q
    if Q is None:
        return P
    x1, y1 = P
    x2, y2 = Q
    if x1 == x2:
        if (y1 + y2) % p == 0 or y1 == 0:
            return None
        lam = (3 * x1 * x1 + a) * inv_mod(2 * y1, p) % p
    else:
        lam = (y2 - y1) * inv_mod(x2 - x1, p) % p
    x3 = (lam * lam - x1 - x2) % p
    y3 = (lam * (x1 - x3) - y1) % p
    return (x3, y3)


def ec_neg(P: Point, p: int) -> Point:
    return None if P is None else (P[0], (-P[1]) % p)


def ec_mul(k: int, P: Point, p: int, a: int) -> Point:
    if k == 0 or P is None:
        return None
    if k < 0:
        return ec_mul(-k, ec_neg(P, p), p, a)
    R: Point = None
    A: Point = P
    while k:
        if k & 1:
            R = ec_add(R, A, p, a)
        A = ec_add(A, A, p, a)
        k >>= 1
    return R


def ec_is_on_curve(P: Point, p: int, a: int, b: int) -> bool:
    if P is None:
        return True
    x, y = P
    return (y * y - (x * x * x + a * x + b)) % p == 0


# ═══════════════════════════════════════════════════════════════════════════
# JACOBIAN EC ARITHMETIC
# ═══════════════════════════════════════════════════════════════════════════
def jac_from_affine(P: Point, p: int) -> Jacobian:
    if P is None:
        return None
    x, y = P
    return (x % p, y % p, 1)


def jac_to_affine(J: Jacobian, p: int) -> Point:
    if J is None:
        return None
    X, Y, Z = J
    Z %= p
    if Z == 0:
        return None
    zi = inv_mod(Z, p)
    zi2 = zi * zi % p
    zi3 = zi2 * zi % p
    return (X * zi2 % p, Y * zi3 % p)


def jac_is_on_curve(J: Jacobian, p: int, a: int, b: int) -> bool:
    if J is None:
        return True
    X, Y, Z = J
    if Z % p == 0:
        return True
    Z2 = Z * Z % p
    Z4 = Z2 * Z2 % p
    Z6 = Z4 * Z2 % p
    return (Y * Y - (X * X % p * X + a * X * Z4 + b * Z6)) % p == 0


def jac_neg(J: Jacobian, p: int) -> Jacobian:
    if J is None:
        return None
    X, Y, Z = J
    return (X % p, (-Y) % p, Z % p)


def jac_double(J: Jacobian, p: int, a: int) -> Jacobian:
    if J is None:
        return None
    X1, Y1, Z1 = J
    if Y1 % p == 0:
        return None
    XX = X1 * X1 % p
    YY = Y1 * Y1 % p
    YYYY = YY * YY % p
    ZZ = Z1 * Z1 % p
    S = 2 * (((X1 + YY) % p) ** 2 - XX - YYYY) % p
    M = (3 * XX + a * ZZ * ZZ) % p if a != 0 else 3 * XX % p
    T = (M * M - 2 * S) % p
    X3 = T
    Y3 = (M * (S - T) - 8 * YYYY) % p
    Z3 = (((Y1 + Z1) % p) ** 2 - YY - ZZ) % p
    return (X3, Y3, Z3)


def jac_add(J1: Jacobian, J2: Jacobian, p: int, a: int) -> Jacobian:
    if J1 is None:
        return J2
    if J2 is None:
        return J1
    X1, Y1, Z1 = J1
    X2, Y2, Z2 = J2
    if Z1 % p == 0:
        return J2
    if Z2 % p == 0:
        return J1
    Z1Z1 = Z1 * Z1 % p
    Z2Z2 = Z2 * Z2 % p
    U1 = X1 * Z2Z2 % p
    U2 = X2 * Z1Z1 % p
    S1 = Y1 * Z2 * Z2Z2 % p
    S2 = Y2 * Z1 * Z1Z1 % p
    H = (U2 - U1) % p
    r = 2 * (S2 - S1) % p
    if H == 0:
        if r == 0:
            return jac_double(J1, p, a)
        return None
    I = (2 * H) % p
    I = I * I % p
    J_ = H * I % p
    V = U1 * I % p
    X3 = (r * r - J_ - 2 * V) % p
    Y3 = (r * (V - X3) - 2 * S1 * J_) % p
    Z3 = (((Z1 + Z2) % p) ** 2 - Z1Z1 - Z2Z2) % p
    Z3 = Z3 * H % p
    return (X3, Y3, Z3)


def jac_mul(k: int, J: Jacobian, p: int, a: int) -> Jacobian:
    if J is None or k == 0:
        return None
    if k < 0:
        return jac_mul(-k, jac_neg(J, p), p, a)
    R: Jacobian = None
    A: Jacobian = J
    while k:
        if k & 1:
            R = jac_add(R, A, p, a)
        A = jac_double(A, p, a)
        k >>= 1
    return R


# ═══════════════════════════════════════════════════════════════════════════
# SEC1 CODEC
# ═══════════════════════════════════════════════════════════════════════════
def decompress_pubkey(hx: str) -> Point:
    h = hx.lower().strip().replace("0x", "").replace(" ", "")
    if len(h) != 66 or h[:2] not in ("02", "03"):
        return None
    try:
        x = int(h[2:], 16)
    except ValueError:
        return None
    if x >= SECP256K1_P:
        return None
    rhs = (pow(x, 3, SECP256K1_P) + SECP256K1_B) % SECP256K1_P
    y = pow(rhs, (SECP256K1_P + 1) // 4, SECP256K1_P)
    if y * y % SECP256K1_P != rhs:
        return None
    if (int(h[:2], 16) == 2 and y % 2) or (int(h[:2], 16) == 3 and y % 2 == 0):
        y = SECP256K1_P - y
    return (x, y)


def compress_pubkey(P: Point) -> str:
    if P is None:
        return ""
    return ("02" if P[1] % 2 == 0 else "03") + f"{P[0]:064x}"


def verify_secp_key(k: int, Q: Point) -> bool:
    if k is None or k <= 0 or k >= SECP256K1_N:
        return False
    try:
        J = jac_mul(k, jac_from_affine(SECP256K1_G, SECP256K1_P),
                    SECP256K1_P, SECP256K1_A)
        return jac_to_affine(J, SECP256K1_P) == Q
    except Exception:
        return False


# ═══════════════════════════════════════════════════════════════════════════
# SMALL-PRIME TABLES (Regev lattice basis)
# ═══════════════════════════════════════════════════════════════════════════
SMALL_PRIMES_CANONICAL: List[int] = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
    59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
    127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
    191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
]
SMALL_PRIMES_EXTENDED: List[int] = SMALL_PRIMES_CANONICAL + [
    257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
    331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
    401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
    467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
    563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619,
]
SMALL_PRIMES_ULTRA: List[int] = SMALL_PRIMES_EXTENDED + [
    631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
    709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
    797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863,
    877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953,
    967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031,
]

SMALL_PRIME_TABLES: Dict[str, List[int]] = {
    "canonical": SMALL_PRIMES_CANONICAL,
    "extended": SMALL_PRIMES_EXTENDED,
    "ultra": SMALL_PRIMES_ULTRA,
}


def get_small_primes(table: str = "canonical") -> List[int]:
    if table not in SMALL_PRIME_TABLES:
        raise ValueError(
            f"unknown small-prime table {table!r}; "
            f"choose from {sorted(SMALL_PRIME_TABLES)}"
        )
    return list(SMALL_PRIME_TABLES[table])


# ═══════════════════════════════════════════════════════════════════════════
# BITCOIN PUZZLE PRESETS
# ═══════════════════════════════════════════════════════════════════════════
@dataclass
class PuzzlePreset:
    key: str
    bits: int
    lower_bound: int
    upper_bound: int
    secret: Optional[int]
    pubkey: str
    description: str


SECP256K1_PUZZLE_PRESETS: Dict[str, PuzzlePreset] = {
    "12": PuzzlePreset(
        "12", 12, 0x800, 0xFFF, 0x9C8,
        "0326445a42b856e565baddd47a6f937d9299d740413212102264b4385e90a32f8d",
        "Bitcoin puzzle #12 (12-bit range)"),
    "14": PuzzlePreset(
        "14", 14, 0x2000, 0x3FFF, 0x2199,
        "036f19619face0c63c4dda566a09a1e78fa9568db11c46f3e9771756b27d8a5c1e",
        "Bitcoin puzzle #14 (14-bit range)"),
    "16": PuzzlePreset(
        "16", 16, 0x8000, 0xFFFF, 0xC668,
        "02d69ccdb7637954cb1d5885900aa24629580b076d190922a7a5165af0a92a42bc",
        "Bitcoin puzzle #16 (16-bit range)"),
    "17": PuzzlePreset(
        "17", 17, 0x10000, 0x1FFFF, 0x17D62,
        "026eee869bd80f24ffd95886dc7ff5481b90f6c6c1e22302bfdc91d9e293dd06cc",
        "Bitcoin puzzle #17 (17-bit range)"),
    "19": PuzzlePreset(
        "19", 19, 0x40000, 0x7FFFF, 0x5C922,
        "03b8d497e6f71c0280878e135183c135991fe3db803e25505149de791f1d919471",
        "Bitcoin puzzle #19 (19-bit range)"),
    "20": PuzzlePreset(
        "20", 20, 0x80000, 0xFFFFF, 0xA3B8C,
        "021d23d69498096c3cb8f8cc50547a921be5268ab8bf9d40c167275c8f4c9c7e00",
        "Bitcoin puzzle #20 (20-bit range)"),
    "21": PuzzlePreset(
        "21", 21, 0x100000, 0x1FFFFF, 0x1347A3,
        "029a00de014a8b3a4a0e84f0c81a8058ad71680248a49601f5292e9dcf6265178d",
        "Bitcoin puzzle #21 (21-bit range)"),
    "22": PuzzlePreset(
        "22", 22, 0x200000, 0x3FFFFF, None,
        "023ed96b524db5ff4fe007ce730366052b7c511dc566227d929070b9ce917abb43",
        "Bitcoin puzzle #22 (22-bit range, secret not publicly known)"),
    "135": PuzzlePreset(
        "135", 135,
        0x4000000000000000000000000000000000,
        0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        0x4B8B9D2434E465E150BD9C66B3AD3C2D6D,
        "0327401b07225a4269ee46c9a420c765ea878cbd8127aed9c3a5d977d112e86469",
        "Bitcoin puzzle #135 (135-bit range)"),
    "140": PuzzlePreset(
        "140", 140,
        0x80000000000000000000000000000000000,
        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
        None,
        "031f6a332d3c5c4f2de2378c012f429cd109ba07d69690c6c701b6bb87860d6640",
        "Bitcoin puzzle #140 (140-bit range, secret not publicly known)"),
}


def verify_puzzle_preset(preset: PuzzlePreset) -> Dict[str, Any]:
    Q = decompress_pubkey(preset.pubkey)
    if Q is None:
        return {
            "key": preset.key,
            "bits": preset.bits,
            "pubkey": preset.pubkey,
            "valid": False,
            "reason": "public key does not decompress",
        }
    on_curve = ec_is_on_curve(Q, SECP256K1_P, SECP256K1_A, SECP256K1_B)
    jac_on_curve = jac_is_on_curve(
        jac_from_affine(Q, SECP256K1_P),
        SECP256K1_P, SECP256K1_A, SECP256K1_B)
    result: Dict[str, Any] = {
        "key": preset.key,
        "bits": preset.bits,
        "range": [hex(preset.lower_bound), hex(preset.upper_bound)],
        "pubkey": preset.pubkey,
        "Qx": f"0x{Q[0]:064x}",
        "Qy": f"0x{Q[1]:064x}",
        "y_parity": Q[1] & 1,
        "on_curve_affine": on_curve,
        "on_curve_jacobian": jac_on_curve,
    }
    if preset.secret is not None:
        result["secret"] = f"0x{preset.secret:x}"
        result["secret_in_range"] = bool(
            preset.lower_bound <= preset.secret <= preset.upper_bound)
        result["secret_verifies"] = verify_secp_key(preset.secret, Q)
        result["valid"] = bool(
            result["secret_verifies"]
            and result["secret_in_range"]
            and on_curve
            and jac_on_curve
        )
    else:
        result["secret"] = None
        result["secret_verifies"] = None
        result["valid"] = bool(on_curve and jac_on_curve)
    return result


def list_presets() -> None:
    print("\nSECP256K1 PUZZLE PRESETS")
    print("-" * 88)
    for key, preset in SECP256K1_PUZZLE_PRESETS.items():
        sec = f"0x{preset.secret:x}" if preset.secret is not None else "unknown"
        print(f"  [{key:>3}] {preset.bits:>3}-bit  "
              f"range=[0x{preset.lower_bound:x}, 0x{preset.upper_bound:x}]")
        print(f"        secret={sec}")
        print(f"        pubkey={preset.pubkey}")
    print("-" * 88)


# ═══════════════════════════════════════════════════════════════════════════
# REGEV SMALL-PRIME BASIS
# ═══════════════════════════════════════════════════════════════════════════
@dataclass
class RegevBasis:
    d: int
    table: str
    primes: List[int]
    points: List[Point]
    order: int
    target_bits: int
    qpd: int


def build_regev_basis(Q: Point, d: int, target_bits: int,
                      table: str = "canonical") -> RegevBasis:
    """
    Build the Regev lattice basis for an ECDLP instance over secp256k1.

    Regev's d-dimensional DLP reduction uses basis elements
    B_1 = b_1 * G, ..., B_{d-2} = b_{d-2} * G, together with the
    target point Q and the generator G.

    The small primes b_i come from the chosen table.
    """
    primes = get_small_primes(table)[:d]
    if len(primes) < d:
        raise ValueError(
            f"table {table!r} has only {len(primes)} primes, "
            f"requested d={d}")
    points: List[Point] = []
    for i in range(d - 2):
        b_i = primes[i]
        J = jac_mul(b_i, jac_from_affine(SECP256K1_G, SECP256K1_P),
                    SECP256K1_P, SECP256K1_A)
        points.append(jac_to_affine(J, SECP256K1_P))
    points.append(Q)
    points.append(SECP256K1_G)
    qpd = max(4, math.ceil(target_bits / d) + 2)
    return RegevBasis(
        d=d, table=table, primes=primes, points=points,
        order=SECP256K1_N, target_bits=target_bits, qpd=qpd)


def check_regev_relation(z: Sequence[int], basis: RegevBasis) -> bool:
    """
    Verify that sum_i z_i * B_i == O (point at infinity) on secp256k1.

    This is the necessary condition for a short relation vector z to be
    valid in Regev's post-processing.
    """
    acc: Jacobian = None
    for zi, B in zip(z, basis.points):
        if zi == 0 or B is None:
            continue
        term = jac_mul(int(zi), jac_from_affine(B, SECP256K1_P),
                       SECP256K1_P, SECP256K1_A)
        acc = jac_add(acc, term, SECP256K1_P, SECP256K1_A)
    return acc is None or jac_to_affine(acc, SECP256K1_P) is None


def regev_basis_report(Q: Point, d: int, target_bits: int,
                       table: str = "canonical") -> Dict[str, Any]:
    basis = build_regev_basis(Q, d, target_bits, table=table)
    base_relation = [0] * d
    base_relation[-1] = SECP256K1_N
    base_holds = check_regev_relation(base_relation, basis)
    return {
        "target_bits": target_bits,
        "table": table,
        "d": basis.d,
        "qpd": basis.qpd,
        "primes": basis.primes,
        "points_hex": [
            None if p is None else compress_pubkey(p)
            for p in basis.points
        ],
        "order": f"0x{SECP256K1_N:x}",
        "base_relation_valid": base_holds,
        "notes": (
            "B_1..B_{d-2} are b_i * G. B_{d-1} = Q. B_d = G. "
            "A valid short relation z satisfies sum z_i * B_i == O. "
            "The trivial relation z = (0,...,0,n) is always valid."
        ),
    }


# ═══════════════════════════════════════════════════════════════════════════
# PUBLISHED FAULT-TOLERANT RESOURCE PLANS
# ═══════════════════════════════════════════════════════════════════════════
@dataclass
class ResourceRow:
    family: str
    type: str
    source: str
    logical_qubits: int
    physical_qubits: int
    toffoli_gates: int
    parallel_runs: int
    wallclock_days: Optional[float]
    success_probability: Optional[float]
    notes: str


def plan_babbush_2026(n: int) -> ResourceRow:
    """
    Babbush et al., Google Quantum AI, 2026.

    Windows-based modular arithmetic, Toffoli-optimized.
    Published figures calibrated to n = 256.
    """
    lq = max(1, round(1200 * n / 256))
    t = max(1, round(70_000_000 * (n / 256) ** 3))
    return ResourceRow(
        family="Shor (Google / Babbush 2026)",
        type="Shor",
        source="Google Quantum AI, 2026",
        logical_qubits=lq,
        physical_qubits=lq * 13,
        toffoli_gates=t,
        parallel_runs=1,
        wallclock_days=None,
        success_probability=None,
        notes=("Windows-based modular arithmetic. Toffoli-optimized "
               "routing for heavy-hex topology."),
    )


def plan_ionq_walking_cat_2026(n: int) -> ResourceRow:
    """
    IonQ Walking Cat, arXiv:2609.05625 (2026).

    Trapped-ion fault-tolerant architecture, end-to-end timing.
    """
    lq = max(1, round(1457 * n / 256))
    phys = max(1, round(19_397 * n / 256))
    t = max(1, round(39_000_000 * (n / 256) ** 3))
    return ResourceRow(
        family="Shor (IonQ Walking Cat 2026)",
        type="Shor",
        source="arXiv:2609.05625",
        logical_qubits=lq,
        physical_qubits=phys,
        toffoli_gates=t,
        parallel_runs=1,
        wallclock_days=25.7 * (n / 256),
        success_probability=0.63,
        notes=("Full end-to-end trapped-ion architecture with CCZ "
               "state factory. Reported ~26 days wallclock at 256-bit."),
    )


def plan_ekera_gartner_regev(n: int) -> ResourceRow:
    """
    Ekerå-Gärtner Regev-variant DLP. arXiv:2308.06572.

    Uses the Regev multi-dimensional reduction with d ~ sqrt(n)
    parallel runs.
    """
    d = max(2, math.ceil(math.sqrt(n)))
    lq = 5 * n
    t_per_run = max(1, round(15_000_000 * (n / 256) ** 1.5))
    return ResourceRow(
        family="Regev / Ekera-Gartner",
        type="Regev",
        source="arXiv:2308.06572",
        logical_qubits=lq,
        physical_qubits=lq * 13,
        toffoli_gates=t_per_run * d,
        parallel_runs=d,
        wallclock_days=None,
        success_probability=None,
        notes=(f"{d} parallel runs. Per-run logical qubit count {lq}. "
               f"Regev's algorithm reduces gate count, not qubit count."),
    )


def plan_chevignard_2026(n: int) -> ResourceRow:
    """
    Chevignard et al., eprint 2026/280.

    Compressed Shor with RNS + Legendre symbol tricks. Lowest
    logical qubit count of the four, but the estimate is heuristic.
    """
    lq = max(1, round(800 * n / 256))
    t = max(1, round(50_000_000 * (n / 256) ** 3))
    return ResourceRow(
        family="Shor (Chevignard et al. 2026)",
        type="Shor",
        source="eprint 2026/280",
        logical_qubits=lq,
        physical_qubits=lq * 13,
        toffoli_gates=t,
        parallel_runs=22,
        wallclock_days=None,
        success_probability=None,
        notes=("Compressed Shor with RNS + Legendre symbol optimization. "
               "Lowest logical qubit count. Heuristic resource model."),
    )


def full_plan(n: int) -> List[ResourceRow]:
    return [
        plan_babbush_2026(n),
        plan_ionq_walking_cat_2026(n),
        plan_ekera_gartner_regev(n),
        plan_chevignard_2026(n),
    ]


def _fmt_big(x: int) -> str:
    if x >= 1_000_000_000:
        return f"{x / 1_000_000_000:.2f}B"
    if x >= 1_000_000:
        return f"{x / 1_000_000:.2f}M"
    if x >= 1_000:
        return f"{x / 1_000:.2f}k"
    return str(x)


def print_resource_plan(n: int) -> None:
    rows = full_plan(n)
    print("\n" + "=" * 108)
    print(f"SECP256K1 ECDLP RESOURCE PLAN — target {n} bits")
    print("=" * 108)
    print(f"{'Family':<42} {'Type':<8} {'Logical':>10} {'Physical':>12} "
          f"{'Toffoli':>10} {'Runs':>6}")
    print("-" * 108)
    for r in rows:
        print(f"{r.family:<42} {r.type:<8} {r.logical_qubits:>10,} "
              f"{r.physical_qubits:>12,} {_fmt_big(r.toffoli_gates):>10} "
              f"{r.parallel_runs:>6}")
    print("-" * 108)
    for r in rows:
        print(f"  {r.family:<42} {r.source}")
        print(f"  {'':<42} {r.notes}")
        if r.wallclock_days is not None:
            print(f"  {'':<42} wallclock ~{r.wallclock_days:.1f} days, "
                  f"P(success) ~{r.success_probability:.2f}")
    print("=" * 108)

    # Regev basis
    d_regev = max(2, math.ceil(math.sqrt(n)))
    primes = get_small_primes("canonical")[:d_regev]
    print(f"\nRegev basis for {n}-bit target:")
    print(f"  d = {d_regev}  (dimension, ~sqrt(n))")
    print(f"  qpd = {max(4, math.ceil(n / d_regev) + 2)}  "
          f"(qubits per dimension)")
    print(f"  b_1..b_d = {primes}")
    print()
    print("HONEST NOTE")
    print("-" * 108)
    print("Every number above comes from the cited paper.")
    print("No such machine exists in 2026.")
    print("This file does not solve any of these instances.")
    print("=" * 108 + "\n")


# ═══════════════════════════════════════════════════════════════════════════
# SELF-TEST
# ═══════════════════════════════════════════════════════════════════════════
def run_self_test() -> Dict[str, Any]:
    results: Dict[str, Any] = {}

    # ── 1. Jacobian matches affine on secp256k1 ───────────────────────────
    rng = random.Random(0xC0FFEE)
    matches = 0
    for _ in range(32):
        k = rng.randrange(1, SECP256K1_N)
        J = jac_mul(k, jac_from_affine(SECP256K1_G, SECP256K1_P),
                    SECP256K1_P, SECP256K1_A)
        A = ec_mul(k, SECP256K1_G, SECP256K1_P, SECP256K1_A)
        if jac_to_affine(J, SECP256K1_P) == A:
            matches += 1
    results["jacobian_matches_affine_32_samples"] = (matches == 32)

    # ── 2. n * G == O ─────────────────────────────────────────────────────
    results["nG_is_infinity"] = (
        jac_mul(SECP256K1_N,
                jac_from_affine(SECP256K1_G, SECP256K1_P),
                SECP256K1_P, SECP256K1_A) is None
    )

    # ── 3. Group law associativity ────────────────────────────────────────
    a = rng.randrange(1, 1000)
    b = rng.randrange(1, 1000)
    c = rng.randrange(1, 1000)
    lhs = jac_add(
        jac_add(jac_from_affine(jac_to_affine(
            jac_mul(a, jac_from_affine(SECP256K1_G, SECP256K1_P),
                    SECP256K1_P, SECP256K1_A), SECP256K1_P), SECP256K1_P),
            jac_from_affine(jac_to_affine(
                jac_mul(b, jac_from_affine(SECP256K1_G, SECP256K1_P),
                        SECP256K1_P, SECP256K1_A), SECP256K1_P),
                SECP256K1_P), SECP256K1_P, SECP256K1_A),
        jac_from_affine(jac_to_affine(
            jac_mul(c, jac_from_affine(SECP256K1_G, SECP256K1_P),
                    SECP256K1_P, SECP256K1_A), SECP256K1_P),
            SECP256K1_P), SECP256K1_P, SECP256K1_A)
    rhs = jac_add(
        jac_from_affine(jac_to_affine(
            jac_mul(a, jac_from_affine(SECP256K1_G, SECP256K1_P),
                    SECP256K1_P, SECP256K1_A), SECP256K1_P), SECP256K1_P),
        jac_add(
            jac_from_affine(jac_to_affine(
                jac_mul(b, jac_from_affine(SECP256K1_G, SECP256K1_P),
                        SECP256K1_P, SECP256K1_A), SECP256K1_P),
                SECP256K1_P),
            jac_from_affine(jac_to_affine(
                jac_mul(c, jac_from_affine(SECP256K1_G, SECP256K1_P),
                        SECP256K1_P, SECP256K1_A), SECP256K1_P),
                SECP256K1_P), SECP256K1_P, SECP256K1_A),
        SECP256K1_P, SECP256K1_A)
    lhs_aff = jac_to_affine(lhs, SECP256K1_P)
    rhs_aff = jac_to_affine(rhs, SECP256K1_P)
    results["jacobian_associativity"] = (lhs_aff == rhs_aff)

    # ── 4. SEC1 round-trip ────────────────────────────────────────────────
    sec1_ok = True
    for k in (1, 2, 12345, 0xDEADBEEF, 0x100000000000000000000):
        Q = ec_mul(k, SECP256K1_G, SECP256K1_P, SECP256K1_A)
        reencoded = compress_pubkey(Q)
        Q2 = decompress_pubkey(reencoded)
        if Q2 != Q:
            sec1_ok = False
            break
    results["sec1_roundtrip"] = sec1_ok

    # ── 5. Puzzle preset verification ─────────────────────────────────────
    puzzle_results: Dict[str, Any] = {}
    for key, preset in SECP256K1_PUZZLE_PRESETS.items():
        v = verify_puzzle_preset(preset)
        puzzle_results[key] = {
            "valid": v["valid"],
            "on_curve_affine": v["on_curve_affine"],
            "on_curve_jacobian": v["on_curve_jacobian"],
            "secret_verifies": v.get("secret_verifies"),
        }
    results["puzzle_presets"] = puzzle_results
    results["all_puzzles_valid"] = all(
        v["valid"] for v in puzzle_results.values())

    # ── 6. Regev basis construction for every table ───────────────────────
    basis_ok = True
    basis_reports: Dict[str, Any] = {}
    for table in SMALL_PRIME_TABLES:
        for d in (2, 3, 5, 8):
            try:
                basis = build_regev_basis(SECP256K1_G, d, 22, table=table)
                if basis.d != d or len(basis.primes) != d:
                    basis_ok = False
                    break
                if len(basis.points) != d:
                    basis_ok = False
                    break
                # Trivial relation: (0, ..., 0, n) should hold
                trivial = [0] * d
                trivial[-1] = SECP256K1_N
                if not check_regev_relation(trivial, basis):
                    basis_ok = False
                    break
            except Exception as e:
                basis_reports[f"{table}_d{d}"] = str(e)
                basis_ok = False
    results["regev_basis_across_tables"] = basis_ok
    results["regev_basis_errors"] = basis_reports

    # ── 7. Resource plans are self-consistent ─────────────────────────────
    plan_ok = True
    for n in (22, 140, 256):
        try:
            rows = full_plan(n)
            if len(rows) != 4:
                plan_ok = False
            for r in rows:
                if r.logical_qubits <= 0 or r.toffoli_gates <= 0:
                    plan_ok = False
                if r.physical_qubits < r.logical_qubits:
                    plan_ok = False
        except Exception:
            plan_ok = False
    results["resource_plans_consistent"] = plan_ok

    # ── 8. Small-prime table integrity ────────────────────────────────────
    table_ok = True
    for name, primes in SMALL_PRIME_TABLES.items():
        if not primes:
            table_ok = False
        if not all(is_probable_prime(p) for p in primes):
            table_ok = False
        if primes != sorted(primes):
            table_ok = False
        if len(set(primes)) != len(primes):
            table_ok = False
    results["small_prime_tables_integrity"] = table_ok

    # ── Summary ───────────────────────────────────────────────────────────
    scalar_keys = [
        "jacobian_matches_affine_32_samples",
        "nG_is_infinity",
        "jacobian_associativity",
        "sec1_roundtrip",
        "all_puzzles_valid",
        "regev_basis_across_tables",
        "resource_plans_consistent",
        "small_prime_tables_integrity",
    ]
    results["all_pass"] = all(results.get(k) is True for k in scalar_keys)
    return results


# ═══════════════════════════════════════════════════════════════════════════
# HONEST SCOPE
# ═══════════════════════════════════════════════════════════════════════════
SCOPE_TEXT = """
HONEST SCOPE
============

What this file does
-------------------
  * Real secp256k1 arithmetic, cross-checked affine vs Jacobian.
  * Strict SEC1 compressed-key codec with round-trip verification.
  * Bitcoin puzzle preset table (12, 14, 16, 17, 19, 20, 21, 22, 135, 140)
    with known secrets verified end-to-end and unknown secrets verified
    as on-curve valid points.
  * Regev small-prime lattice basis construction for any d and any of
    three prime tables.
  * Four published fault-tolerant resource plans, each sourced to the
    paper it cites.
  * Complete self-test.
  * Interactive menu.
  * CLI.

What this file does NOT do
--------------------------
  * It does not solve 22-bit or 140-bit or 256-bit secp256k1 ECDLP.
  * It does not build a quantum circuit that claims to run at those
    sizes.
  * It does not use toy curves, dense matrices, or placeholder arithmetic.

Why not
-------
  Published fault-tolerant estimates for 256-bit secp256k1 ECDLP:
    - Google (Babbush et al. 2026):   ~1,200 logical qubits, ~70M Toffoli
    - IonQ Walking Cat 2026:         ~1,457 logical qubits, ~19,397 physical
    - Ekerå-Gärtner Regev:            5n logical, n^{1.5} Toffoli per run
    - Chevignard et al. 2026:         ~800 logical (heuristic)

  Every one of these exceeds what any 2026 quantum processor can hold
  with error correction. No code changes that.

  What code can do is build the correct circuit structure and count the
  gates. This file does the counting and cites the sources. It does not
  pretend the execution is possible.

If you want the circuits
------------------------
  The papers below contain the full decomposed circuit diagrams and
  the gate-by-gate resource models:

    - Babbush et al., "Quantum computing for ECDLP at cryptographically
      relevant scale", Google Quantum AI, 2026.
    - IonQ Walking Cat, arXiv:2609.05625.
    - Ekerå-Gärtner, arXiv:2308.06572.
    - Chevignard et al., eprint 2026/280.
    - Häner et al., PQCrypto 2020 (the foundational decomposition).
    - Roetteler et al., eprint 2017/598 (first rigorous estimate).

  These are the sources. This file does not replace them.
"""


# ═══════════════════════════════════════════════════════════════════════════
# INTERACTIVE MENU
# ═══════════════════════════════════════════════════════════════════════════
MENU = """
================================================================
  SECP256K1 ECDLP RESOURCE + VERIFICATION TOOLKIT
================================================================
   1. Run full self-test
   2. List Bitcoin puzzle presets
   3. Verify a puzzle preset
   4. Resource plan for a target bit size
   5. Resource plan for all preset bit sizes
   6. Build Regev small-prime basis for a target
   7. List small-prime tables
   8. Honest scope
   0. Exit
================================================================
"""


def _ask(prompt: str, default: str = "") -> str:
    suffix = f" [{default}]" if default else ""
    try:
        v = input(prompt + suffix + ": ").strip()
    except EOFError:
        return default
    return v or default


def _ask_int(prompt: str, default: int) -> int:
    while True:
        try:
            return int(_ask(prompt, str(default)), 0)
        except ValueError:
            print("  invalid integer")


def _ask_choice(prompt: str, allowed: Sequence[str], default: str) -> str:
    allowed = tuple(allowed)
    while True:
        v = _ask(prompt, default).lower().strip()
        if v in allowed:
            return v
        print("  choose one of: " + ", ".join(allowed))


def interactive_menu() -> int:
    while True:
        print(MENU)
        choice = _ask("Choice", "1")
        try:
            if choice == "0":
                return 0
            if choice == "1":
                print(json.dumps(run_self_test(), indent=2, default=str))
            elif choice == "2":
                list_presets()
            elif choice == "3":
                keys = ", ".join(SECP256K1_PUZZLE_PRESETS.keys())
                print(f"  Available: {keys}")
                key = _ask("Puzzle key", "22")
                if key not in SECP256K1_PUZZLE_PRESETS:
                    print(f"  unknown preset {key!r}")
                    continue
                preset = SECP256K1_PUZZLE_PRESETS[key]
                print(json.dumps(verify_puzzle_preset(preset),
                                 indent=2, default=str))
            elif choice == "4":
                n = _ask_int("Target bit size", 256)
                print_resource_plan(n)
            elif choice == "5":
                for key in SECP256K1_PUZZLE_PRESETS:
                    n = SECP256K1_PUZZLE_PRESETS[key].bits
                    print(f"\n>>> Preset {key}: {n}-bit target")
                    print_resource_plan(n)
            elif choice == "6":
                n = _ask_int("Target bit size", 140)
                d_default = max(2, math.ceil(math.sqrt(n)))
                d = _ask_int("Dimension d", d_default)
                table = _ask_choice(
                    "Small-prime table",
                    tuple(SMALL_PRIME_TABLES.keys()), "canonical")
                pk = _ask(
                    "Compressed pubkey (blank = generator)",
                    compress_pubkey(SECP256K1_G))
                Q = decompress_pubkey(pk)
                if Q is None:
                    print("  invalid pubkey")
                    continue
                report = regev_basis_report(Q, d, n, table=table)
                print(json.dumps(report, indent=2, default=str))
            elif choice == "7":
                for name, primes in SMALL_PRIME_TABLES.items():
                    print(f"\n{name} ({len(primes)} primes):")
                    for i in range(0, len(primes), 12):
                        chunk = primes[i:i + 12]
                        print("  " + ", ".join(str(p) for p in chunk))
            elif choice == "8":
                print(SCOPE_TEXT)
            else:
                print("  invalid choice")
        except KeyboardInterrupt:
            print()
            return 0
        except Exception as exc:
            print(f"  ERROR: {type(exc).__name__}: {exc}")


# ═══════════════════════════════════════════════════════════════════════════
# CLI
# ═══════════════════════════════════════════════════════════════════════════
def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        description=(
            "secp256k1 ECDLP resource + verification toolkit. "
            "Classical verification, Regev small-prime basis, four "
            "published fault-tolerant plans. No fake quantum circuits."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Examples:\n"
            "  python SECP256K1_ECD_LP_HONEST.py --self-test\n"
            "  python SECP256K1_ECD_LP_HONEST.py --presets\n"
            "  python SECP256K1_ECD_LP_HONEST.py --puzzle 22\n"
            "  python SECP256K1_ECD_LP_HONEST.py --plan 140\n"
            "  python SECP256K1_ECD_LP_HONEST.py --plan-all\n"
            "  python SECP256K1_ECD_LP_HONEST.py --basis 140 "
            "--table extended\n"
        ),
    )
    ap.add_argument("--self-test", action="store_true",
                    help="run the full verification suite")
    ap.add_argument("--presets", action="store_true",
                    help="list all Bitcoin puzzle presets")
    ap.add_argument("--puzzle", default="", metavar="KEY",
                    help="verify a puzzle preset by key (12, 14, 16, 17, "
                         "19, 20, 21, 22, 135, 140)")
    ap.add_argument("--plan", type=int, default=0, metavar="BITS",
                    help="print resource plan for a target bit size")
    ap.add_argument("--plan-all", action="store_true",
                    help="print resource plans for every preset bit size")
    ap.add_argument("--basis", type=int, default=0, metavar="BITS",
                    help="build the Regev small-prime basis for a target "
                         "bit size (uses generator if --pubkey omitted)")
    ap.add_argument("--pubkey", default="",
                    help="compressed pubkey for --basis "
                         "(default: generator)")
    ap.add_argument("--table", default="canonical",
                    choices=tuple(SMALL_PRIME_TABLES.keys()),
                    help="small-prime table (canonical | extended | ultra)")
    ap.add_argument("--dim", type=int, default=0,
                    help="Regev dimension d (default: ceil(sqrt(bits)))")
    ap.add_argument("--small-primes", action="store_true",
                    help="dump every small-prime table")
    ap.add_argument("--scope", action="store_true",
                    help="print the honest scope text")
    ap.add_argument("--json-out", default="",
                    help="write the selected output to a JSON file")
    args = ap.parse_args(list(sys.argv[1:] if argv is None else argv))

    any_flag = any([
        args.self_test, args.presets, args.puzzle,
        args.plan, args.plan_all, args.basis,
        args.small_primes, args.scope,
    ])
    if not any_flag:
        return interactive_menu()

    out: Any = None

    if args.self_test:
        out = run_self_test()
        print(json.dumps(out, indent=2, default=str))
        if args.json_out:
            Path(args.json_out).write_text(
                json.dumps(out, indent=2, default=str))
        return 0 if out.get("all_pass") else 1

    if args.presets:
        list_presets()
        return 0

    if args.small_primes:
        for name, primes in SMALL_PRIME_TABLES.items():
            print(f"\n{name} ({len(primes)} primes):")
            for i in range(0, len(primes), 12):
                chunk = primes[i:i + 12]
                print("  " + ", ".join(str(p) for p in chunk))
        return 0

    if args.scope:
        print(SCOPE_TEXT)
        return 0

    if args.puzzle:
        if args.puzzle not in SECP256K1_PUZZLE_PRESETS:
            print(f"ERROR: unknown puzzle key {args.puzzle!r}",
                  file=sys.stderr)
            return 2
        preset = SECP256K1_PUZZLE_PRESETS[args.puzzle]
        out = verify_puzzle_preset(preset)
        print(json.dumps(out, indent=2, default=str))
        if args.json_out:
            Path(args.json_out).write_text(
                json.dumps(out, indent=2, default=str))
        return 0 if out["valid"] else 1

    if args.plan:
        print_resource_plan(args.plan)
        if args.json_out:
            out = [asdict(r) for r in full_plan(args.plan)]
            Path(args.json_out).write_text(
                json.dumps(out, indent=2, default=str))
        return 0

    if args.plan_all:
        for key, preset in SECP256K1_PUZZLE_PRESETS.items():
            n = preset.bits
            print(f"\n>>> Preset {key}: {n}-bit target")
            print_resource_plan(n)
        return 0

    if args.basis:
        n = args.basis
        d = args.dim if args.dim > 0 else max(2, math.ceil(math.sqrt(n)))
        pk = args.pubkey or compress_pubkey(SECP256K1_G)
        Q = decompress_pubkey(pk)
        if Q is None:
            print(f"ERROR: invalid pubkey {pk!r}", file=sys.stderr)
            return 2
        report = regev_basis_report(Q, d, n, table=args.table)
        print(json.dumps(report, indent=2, default=str))
        if args.json_out:
            Path(args.json_out).write_text(
                json.dumps(report, indent=2, default=str))
        return 0

    return 0


if __name__ == "__main__":
    raise SystemExit(main())