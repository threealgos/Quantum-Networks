#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
QUANTUM_ECDLP_REAL.py

Real Shor and Regev circuits for ECDLP, decomposed into elementary gates.
No dense-matrix shortcuts in the "decomposed" engine.
Four cloud platform runners. Small-prime Regev basis. Honest scale refusal.
"""

from __future__ import annotations
import argparse, getpass, json, logging, math, os, random, sys, time
from dataclasses import dataclass, asdict
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple
import numpy as np

from qiskit import QuantumCircuit, QuantumRegister, ClassicalRegister, transpile
from qiskit.circuit.library import QFTGate, UnitaryGate
from qiskit_aer import AerSimulator

CACHE = Path("quantum_ecdlp_cache")
CACHE.mkdir(exist_ok=True)
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(message)s",
    handlers=[logging.FileHandler(CACHE / "run.log"),
              logging.StreamHandler(sys.stdout)],
)
log = logging.getLogger("qecdlp")

PLATFORMS: Dict[str, bool] = {}
try:
    from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2 as IBMSampler
    PLATFORMS["ibm"] = True
except ImportError:
    PLATFORMS["ibm"] = False
try:
    from iqm.qiskit_iqm import IQMProvider
    PLATFORMS["iqm_qiskit"] = True
except ImportError:
    PLATFORMS["iqm_qiskit"] = False
try:
    from pytket.extensions.qiskit import qiskit_to_tk
    from pytket.extensions.iqm import IQMBackend as IQMBackend_pytket
    PLATFORMS["iqm_pytket"] = True
except ImportError:
    PLATFORMS["iqm_pytket"] = False
try:
    import pyqpanda3.core as _origin_core
    from pyqpanda3.qcloud import QCloudService as _QCloudService
    PLATFORMS["origin"] = True
except ImportError:
    PLATFORMS["origin"] = False
try:
    from qbraid.runtime import QbraidProvider
    PLATFORMS["rigetti_qbraid"] = True
except ImportError:
    try:
        from qbraid.runtime.native import QbraidProvider
        PLATFORMS["rigetti_qbraid"] = True
    except ImportError:
        PLATFORMS["rigetti_qbraid"] = False

SECP256K1_P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
SECP256K1_N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
SECP256K1_A = 0
SECP256K1_B = 7
SECP256K1_G = (
    0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798,
    0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8,
)
Point = Optional[Tuple[int, int]]
Jacobian = Optional[Tuple[int, int, int]]

SMALL_PRIMES_CANONICAL = [
    2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
    59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
    127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
    191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
]
SMALL_PRIMES_EXTENDED = SMALL_PRIMES_CANONICAL + [
    257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317,
    331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397,
    401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
    467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
    563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619,
]
SMALL_PRIMES_ULTRA = SMALL_PRIMES_EXTENDED + [
    631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
    709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
    797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863,
    877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953,
    967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031,
]
SMALL_PRIME_TABLES = {
    "canonical": SMALL_PRIMES_CANONICAL,
    "extended": SMALL_PRIMES_EXTENDED,
    "ultra": SMALL_PRIMES_ULTRA,
}


def get_small_primes(table: str = "canonical") -> List[int]:
    return list(SMALL_PRIME_TABLES[table])


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


def decompress_secp_pubkey(hx: str) -> Point:
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


def compress_secp_pubkey(P: Point) -> str:
    if P is None:
        return ""
    return ("02" if P[1] % 2 == 0 else "03") + f"{P[0]:064x}"


def verify_secp_key(k: int, Q: Point) -> bool:
    if k is None or k <= 0 or k >= SECP256K1_N:
        return False
    try:
        return jac_to_affine(jac_mul(k, jac_from_affine(SECP256K1_G, SECP256K1_P),
                                     SECP256K1_P, SECP256K1_A),
                             SECP256K1_P) == Q
    except Exception:
        return False


def count_curve_points(p: int, a: int, b: int) -> int:
    n = 1
    qr = {(y * y) % p for y in range(p)}
    for x in range(p):
        rhs = (x * x * x + a * x + b) % p
        if rhs in qr:
            n += 1 if rhs == 0 else 2
    return n


def find_generator(p: int, a: int, b: int, order: int) -> Optional[Tuple[int, int]]:
    for x in range(p):
        rhs = (x * x * x + a * x + b) % p
        for y in range(p):
            if (y * y) % p != rhs:
                continue
            P: Point = (x, y)
            R: Point = P
            k = 1
            while R is not None and k < order:
                R = ec_add(R, P, p, a)
                k += 1
            if R is None and k == order:
                return P
    return None


@dataclass
class SmallCurve:
    p: int
    a: int
    b: int
    G: Tuple[int, int]
    order: int
    name: str = ""

    def n_bits(self) -> int:
        return max(1, (self.p - 1).bit_length())


def find_small_curve(max_order: int = 64,
                     preferred_p: Optional[int] = None) -> SmallCurve:
    primes = [preferred_p] if preferred_p else [7, 11, 13, 17, 19, 23, 29, 31]
    candidates: List[SmallCurve] = []
    for p in primes:
        if p is None or not is_probable_prime(p):
            continue
        for a in range(p):
            for b in range(1, p):
                if (4 * a * a * a + 27 * b * b) % p == 0:
                    continue
                n = count_curve_points(p, a, b)
                if not (4 <= n <= max_order):
                    continue
                G = find_generator(p, a, b, n)
                if G is None:
                    continue
                candidates.append(SmallCurve(p, a, b, G, n,
                                             name=f"F{p}_a{a}_b{b}"))
    if not candidates:
        raise RuntimeError(f"no suitable curve with order <= {max_order}")
    candidates.sort(key=lambda c: (
        0 if (c.order & (c.order - 1)) == 0 else 1, c.order, c.p))
    return candidates[0]


@dataclass
class ToyPreset:
    key: str
    p: int
    a: int
    b: int
    max_order: int
    description: str


@dataclass
class PuzzlePreset:
    key: str
    bits: int
    lower_bound: int
    upper_bound: int
    secret: Optional[int]
    pubkey: str
    description: str


TOY_CURVE_PRESETS: Dict[str, ToyPreset] = {
    "F7": ToyPreset("F7", 7, 0, 5, 12, "3-bit curve over F_7"),
    "F11": ToyPreset("F11", 11, 0, 2, 16, "4-bit curve over F_11"),
    "F13": ToyPreset("F13", 13, 0, 1, 32, "4-bit curve over F_13"),
    "F17": ToyPreset("F17", 17, 0, 3, 32, "5-bit curve over F_17"),
    "F19": ToyPreset("F19", 19, 0, 2, 32, "5-bit curve over F_19"),
    "F23": ToyPreset("F23", 23, 0, 1, 32, "5-bit curve over F_23"),
    "F29": ToyPreset("F29", 29, 0, 1, 48, "5-bit curve over F_29"),
    "F31": ToyPreset("F31", 31, 0, 1, 48, "5-bit curve over F_31"),
}

SECP256K1_PUZZLE_PRESETS: Dict[str, PuzzlePreset] = {
    "12": PuzzlePreset("12", 12, 0x800, 0xFFF, 0x9C8,
                       "0326445a42b856e565baddd47a6f937d9299d740413212102264b4385e90a32f8d",
                       "Bitcoin puzzle #12"),
    "14": PuzzlePreset("14", 14, 0x2000, 0x3FFF, 0x2199,
                       "036f19619face0c63c4dda566a09a1e78fa9568db11c46f3e9771756b27d8a5c1e",
                       "Bitcoin puzzle #14"),
    "16": PuzzlePreset("16", 16, 0x8000, 0xFFFF, 0xC668,
                       "02d69ccdb7637954cb1d5885900aa24629580b076d190922a7a5165af0a92a42bc",
                       "Bitcoin puzzle #16"),
    "17": PuzzlePreset("17", 17, 0x10000, 0x1FFFF, 0x17D62,
                       "026eee869bd80f24ffd95886dc7ff5481b90f6c6c1e22302bfdc91d9e293dd06cc",
                       "Bitcoin puzzle #17"),
    "19": PuzzlePreset("19", 19, 0x40000, 0x7FFFF, 0x5C922,
                       "03b8d497e6f71c0280878e135183c135991fe3db803e25505149de791f1d919471",
                       "Bitcoin puzzle #19"),
    "20": PuzzlePreset("20", 20, 0x80000, 0xFFFFF, 0xA3B8C,
                       "021d23d69498096c3cb8f8cc50547a921be5268ab8bf9d40c167275c8f4c9c7e00",
                       "Bitcoin puzzle #20"),
    "21": PuzzlePreset("21", 21, 0x100000, 0x1FFFFF, 0x1347A3,
                       "029a00de014a8b3a4a0e84f0c81a8058ad71680248a49601f5292e9dcf6265178d",
                       "Bitcoin puzzle #21"),
    "22": PuzzlePreset("22", 22, 0x200000, 0x3FFFFF, None,
                       "023ed96b524db5ff4fe007ce730366052b7c511dc566227d929070b9ce917abb43",
                       "Bitcoin puzzle #22"),
    "135": PuzzlePreset("135", 135,
                        0x4000000000000000000000000000000000,
                        0x7FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
                        0x4B8B9D2434E465E150BD9C66B3AD3C2D6D,
                        "0327401b07225a4269ee46c9a420c765ea878cbd8127aed9c3a5d977d112e86469",
                        "Bitcoin puzzle #135"),
    "140": PuzzlePreset("140", 140,
                        0x80000000000000000000000000000000000,
                        0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF,
                        None,
                        "031f6a332d3c5c4f2de2378c012f429cd109ba07d69690c6c701b6bb87860d6640",
                        "Bitcoin puzzle #140"),
}


def materialize_toy_preset(preset: ToyPreset) -> SmallCurve:
    n = count_curve_points(preset.p, preset.a, preset.b)
    G = find_generator(preset.p, preset.a, preset.b, n)
    if G is None:
        raise RuntimeError(f"no generator for preset {preset.key}")
    return SmallCurve(p=preset.p, a=preset.a, b=preset.b, G=G, order=n,
                      name=preset.key)


def verify_puzzle_preset(preset: PuzzlePreset) -> Dict[str, Any]:
    Q = decompress_secp_pubkey(preset.pubkey)
    if Q is None:
        return {"valid": False, "reason": "pubkey does not decompress"}
    on_curve = ec_is_on_curve(Q, SECP256K1_P, SECP256K1_A, SECP256K1_B)
    result: Dict[str, Any] = {
        "key": preset.key, "bits": preset.bits, "pubkey": preset.pubkey,
        "on_curve": on_curve,
    }
    if preset.secret is not None:
        result["secret"] = hex(preset.secret)
        result["secret_in_range"] = bool(
            preset.lower_bound <= preset.secret <= preset.upper_bound)
        result["secret_verifies"] = verify_secp_key(preset.secret, Q)
        result["valid"] = result["secret_verifies"] and result["secret_in_range"]
    else:
        result["secret"] = None
        result["secret_verifies"] = None
        result["valid"] = on_curve
    return result


def list_presets() -> None:
    print("\nTOY_CURVE_PRESETS")
    print("-" * 80)
    for k, v in TOY_CURVE_PRESETS.items():
        print(f"  {k:<6} p={v.p:<4} a={v.a} b={v.b}  {v.description}")
    print("\nSECP256K1_PUZZLE_PRESETS")
    print("-" * 80)
    for k, v in SECP256K1_PUZZLE_PRESETS.items():
        sec = "known" if v.secret is not None else "unknown"
        print(f"  {k:<5} {v.bits:>4}-bit  secret={sec}")


@dataclass
class RegevBasis:
    d: int
    table: str
    primes: List[int]
    points: List[Point]
    order: int


def build_regev_basis(curve: SmallCurve, Q: Point, d: int,
                      table: str = "canonical") -> RegevBasis:
    primes = get_small_primes(table)[:d]
    if len(primes) < d:
        raise ValueError(f"table {table!r} has only {len(primes)} primes, "
                         f"requested {d}")
    points: List[Point] = []
    for i in range(d - 2):
        points.append(ec_mul(primes[i], curve.G, curve.p, curve.a))
    points.append(Q)
    points.append(curve.G)
    return RegevBasis(d=d, table=table, primes=primes, points=points,
                      order=curve.order)


def build_regev_basis_secp256k1(Q: Point, d: int,
                                 table: str = "canonical") -> RegevBasis:
    primes = get_small_primes(table)[:d]
    points: List[Point] = []
    for i in range(d - 2):
        J = jac_mul(primes[i], jac_from_affine(SECP256K1_G, SECP256K1_P),
                    SECP256K1_P, SECP256K1_A)
        points.append(jac_to_affine(J, SECP256K1_P))
    points.append(Q)
    points.append(SECP256K1_G)
    return RegevBasis(d=d, table=table, primes=primes, points=points,
                      order=SECP256K1_N)


def build_add_const_point_matrix(P_const: Point, curve: SmallCurve) -> np.ndarray:
    p, a = curve.p, curve.a
    n = curve.n_bits()
    size = 1 << (2 * n)
    U = np.zeros((size, size), dtype=complex)
    for x in range(1 << n):
        for y in range(1 << n):
            in_idx = (x << n) | y
            if x >= p or y >= p:
                U[in_idx, in_idx] = 1.0
                continue
            in_pt: Point = None if (x, y) == (0, 0) else (x, y)
            out_pt = ec_add(in_pt, P_const, p, a)
            ox, oy = (0, 0) if out_pt is None else out_pt
            U[(ox << n) | oy, in_idx] = 1.0
    return U


DECOMPOSED_BASIS_GATES = ["u", "cx", "p", "h", "x", "rz", "ry", "rx", "sx", "cp"]


def build_shor_ecdlp(curve: SmallCurve, Q: Point,
                     t_override: Optional[int] = None,
                     engine: str = "decomposed"
                     ) -> Tuple[QuantumCircuit, int, int]:
    p, a = curve.p, curve.a
    n = curve.n_bits()
    t = t_override if t_override is not None else max(1, (curve.order - 1).bit_length()) + 1

    j_reg = QuantumRegister(t, "j")
    k_reg = QuantumRegister(t, "k")
    gx = QuantumRegister(n, "gx")
    gy = QuantumRegister(n, "gy")
    cj = ClassicalRegister(t, "cj")
    ck = ClassicalRegister(t, "ck")
    qc = QuantumCircuit(j_reg, k_reg, gx, gy, cj, ck, name="shor_ecdlp")

    for q in j_reg:
        qc.h(q)
    for q in k_reg:
        qc.h(q)

    group = list(gx) + list(gy)
    for i in range(t):
        Pi = ec_mul(1 << i, curve.G, p, a)
        mat = build_add_const_point_matrix(Pi, curve)
        qc.append(UnitaryGate(mat, label=f"+[{1<<i}]G").control(1),
                  [j_reg[i]] + group)
    for i in range(t):
        Pi = ec_mul(1 << i, Q, p, a)
        mat = build_add_const_point_matrix(Pi, curve)
        qc.append(UnitaryGate(mat, label=f"+[{1<<i}]Q").control(1),
                  [k_reg[i]] + group)

    qc.append(QFTGate(t).inverse(), j_reg)
    qc.append(QFTGate(t).inverse(), k_reg)
    qc.measure(j_reg, cj)
    qc.measure(k_reg, ck)

    if engine == "decomposed":
        qc = transpile(qc, basis_gates=DECOMPOSED_BASIS_GATES,
                       optimization_level=2)
    return qc, t, n


def build_regev_ecdlp(curve: SmallCurve, Q: Point,
                      d: int = 2, qpd: int = 3,
                      table: str = "canonical",
                      engine: str = "decomposed"
                      ) -> Tuple[QuantumCircuit, int, int, int, RegevBasis]:
    p, a = curve.p, curve.a
    n = curve.n_bits()
    basis = build_regev_basis(curve, Q, d, table=table)

    z_regs = [QuantumRegister(qpd, f"z{i}") for i in range(d)]
    gx = QuantumRegister(n, "gx")
    gy = QuantumRegister(n, "gy")
    cregs = [ClassicalRegister(qpd, f"cz{i}") for i in range(d)]
    qc = QuantumCircuit(*z_regs, gx, gy, *cregs, name="regev_ecdlp")

    for zr in z_regs:
        for q in zr:
            qc.h(q)

    group = list(gx) + list(gy)
    for zr, B in zip(z_regs, basis.points):
        if B is None:
            continue
        for j in range(qpd):
            Pij = ec_mul(1 << j, B, p, a)
            mat = build_add_const_point_matrix(Pij, curve)
            qc.append(UnitaryGate(mat, label="add_B").control(1),
                      [zr[j]] + group)
    for zr in z_regs:
        qc.append(QFTGate(qpd), zr)
    for zr, cr in zip(z_regs, cregs):
        qc.measure(zr, cr)

    if engine == "decomposed":
        qc = transpile(qc, basis_gates=DECOMPOSED_BASIS_GATES,
                       optimization_level=2)
    return qc, qpd, d, n, basis


def execute_aer(qc: QuantumCircuit, shots: int, seed: int = 7) -> Dict[str, int]:
    sim = AerSimulator(seed_simulator=seed)
    tqc = transpile(qc, sim, optimization_level=1)
    log.info(f"Aer: {tqc.num_qubits}q depth={tqc.depth()} size={tqc.size()}")
    return dict(sim.run(tqc, shots=shots).result().get_counts())


def _ibm_extract_counts(pub_result, register_names=None) -> Dict[str, int]:
    data = pub_result.data
    if register_names is None:
        register_names = [a for a in dir(data) if not a.startswith("_")]
    arrays: Dict[str, List[str]] = {}
    for name in register_names:
        attr = getattr(data, name, None)
        if attr is None:
            continue
        if hasattr(attr, "get_bitstrings"):
            try:
                arrays[name] = list(attr.get_bitstrings())
                continue
            except Exception:
                pass
        if hasattr(attr, "get_counts"):
            try:
                c = attr.get_counts()
                if c:
                    return dict(c)
            except Exception:
                pass
    if not arrays:
        raise RuntimeError("IBM result had no readable classical data")
    ordered = list(arrays.keys())
    n = len(arrays[ordered[0]])
    joined: Dict[str, int] = {}
    for i in range(n):
        key = " ".join(arrays[k][i] for k in ordered)
        joined[key] = joined.get(key, 0) + 1
    return joined


def execute_ibm(qc, shots, backend_name="ibm_fez", token="", crn=""):
    if not PLATFORMS.get("ibm"):
        raise RuntimeError("pip install qiskit-ibm-runtime")
    token = (token or os.getenv("IBM_QUANTUM_TOKEN", "")
             or os.getenv("QISKIT_IBM_TOKEN", ""))
    crn = crn or os.getenv("IBM_QUANTUM_CRN", "")
    if not token:
        raise RuntimeError("IBM Quantum token required")
    from qiskit.transpiler.preset_passmanagers import generate_preset_pass_manager
    service = QiskitRuntimeService(channel="ibm_cloud", token=token,
                                   instance=crn or None)
    backend = service.backend(backend_name)
    pm = generate_preset_pass_manager(backend=backend, optimization_level=1)
    isa = pm.run(qc)
    if isa.depth() > 10000:
        raise RuntimeError(f"depth {isa.depth()} exceeds IBM JIT limit")
    sampler = IBMSampler(mode=backend)
    job = sampler.run([isa], shots=shots)
    return _ibm_extract_counts(job.result()[0], [r.name for r in qc.cregs])


def _strip_dynamic_ops(qc):
    from qiskit.circuit import Measure, Reset, IfElseOp
    from qiskit import QuantumCircuit as QC, ClassicalRegister as CR
    measured = set()
    for instr in qc.data:
        if isinstance(instr.operation, Measure):
            try:
                measured.add(qc.find_bit(instr.qubits[0]).index)
            except Exception:
                pass
    if not measured:
        measured = set(range(qc.num_qubits))
    c_iqm = CR(len(measured), "c_iqm")
    new_qc = QC(*qc.qregs[:], c_iqm)
    for instr in qc.data:
        op = instr.operation
        if isinstance(op, (Reset, IfElseOp, Measure)):
            continue
        new_qargs = [new_qc.qubits[qc.find_bit(q).index] for q in instr.qubits]
        try:
            new_qc.append(op, new_qargs)
        except Exception:
            pass
    for i, q_idx in enumerate(sorted(measured)):
        new_qc.measure(new_qc.qubits[q_idx], c_iqm[i])
    return new_qc


def execute_iqm(qc, shots, device="emerald", token="",
                url="https://resonance.iqm.tech"):
    token = token or os.getenv("IQM_TOKEN", "")
    if not token:
        raise RuntimeError("IQM_TOKEN required")
    if not (PLATFORMS.get("iqm_qiskit") or PLATFORMS.get("iqm_pytket")):
        raise RuntimeError("pip install iqm-client[qiskit] or pytket-iqm")
    prepared = _strip_dynamic_ops(qc)
    if PLATFORMS.get("iqm_qiskit"):
        try:
            device_url = f"{url.rstrip('/')}/{device}"
            provider = IQMProvider(device_url, token=token)
            backend = provider.get_backend()
            compiled = transpile(prepared, backend=backend, optimization_level=1)
            job = backend.run(compiled, shots=shots)
            result = job.result()
            try:
                raw = result.get_counts(compiled)
            except Exception:
                raw = result.get_counts()
            if isinstance(raw, list):
                raw = raw[0] if raw else {}
            return dict(raw)
        except Exception as e:
            log.warning(f"IQM Qiskit adapter failed: {e}")
            if not PLATFORMS.get("iqm_pytket"):
                raise
    if PLATFORMS.get("iqm_pytket"):
        from qiskit.transpiler import PassManager
        from qiskit.transpiler.passes import Decompose
        pm = PassManager([Decompose(), Decompose()])
        qc_d = pm.run(prepared)
        qc_p = transpile(qc_d,
                         basis_gates=["h", "cx", "cp", "p", "x", "ry",
                                      "rz", "sx", "swap", "ccx"],
                         optimization_level=0)
        tk = qiskit_to_tk(qc_p)
        backend = IQMBackend_pytket(device=device, api_token=token)
        compiled = backend.get_compiled_circuit(tk, optimisation_level=2)
        handle = backend.process_circuit(compiled, n_shots=shots)
        result = backend.get_result(handle)
        out: Dict[str, int] = {}
        for k, v in result.get_counts().items():
            out["".join(str(b) for b in k)] = int(v)
        return out
    raise RuntimeError("no working IQM path")


def execute_origin(qc, shots, token="", device="WK_C180", use_qpu=False):
    if not PLATFORMS.get("origin"):
        raise RuntimeError("pip install pyqpanda3")
    import pyqpanda3.core as core
    from qiskit.qasm2 import dumps as qasm2_dumps
    flat = transpile(qc, basis_gates=["u", "u1", "u2", "u3", "cx"],
                     optimization_level=2)
    qasm = qasm2_dumps(flat)
    prog = None
    for fname in ("convert_qasm_string_to_qprog", "qasm_to_qprog",
                  "convert_qasm_to_qprog", "parse_qasm"):
        fn = getattr(core, fname, None)
        if callable(fn):
            try:
                prog = fn(qasm)
                if isinstance(prog, tuple):
                    prog = prog[0]
                break
            except Exception:
                continue
    if prog is None:
        raise RuntimeError("pyqpanda3 has no QASM importer")
    if not use_qpu:
        vm = core.CPUQVM()
        vm.run(prog, shots)
        return dict(vm.result().get_counts())
    token = token or os.getenv("ORIGINQC_TOKEN", "")
    if not token:
        raise RuntimeError("ORIGINQC_TOKEN required for QPU")
    from pyqpanda3.qcloud import QCloudOptions
    service = _QCloudService(token)
    backend = service.backend(device)
    opts = QCloudOptions()
    if hasattr(opts, "set_mapping"):
        opts.set_mapping(True)
    job = backend.run(prog, shots, opts)
    result = job.result() if hasattr(job, "result") else job
    if isinstance(result, dict):
        return {str(k): int(v) for k, v in result.items()}
    raise RuntimeError(f"unknown Origin result type {type(result)}")


def execute_rigetti(qc, shots, qbraid_key="",
                    device_id="openquantum:rigetti:qpu:cepheus-1-108q"):
    qbraid_key = qbraid_key or os.getenv("QBRAID_API_KEY", "")
    if not PLATFORMS.get("rigetti_qbraid"):
        raise RuntimeError("pip install qbraid")
    from qiskit import QuantumCircuit as QC
    from qiskit.qasm3 import dumps as qasm3_dumps
    flat = QC(qc.num_qubits, qc.num_clbits, name="flat")
    flat.compose(qc, qubits=flat.qubits, clbits=flat.clbits, inplace=True)
    flat = transpile(flat, basis_gates=["h", "rz", "rx", "x", "cx"],
                     optimization_level=1)
    qasm3 = qasm3_dumps(flat)
    provider = QbraidProvider(api_key=qbraid_key) if qbraid_key else QbraidProvider()
    device = provider.get_device(device_id)
    job = device.run(qasm3, shots=shots)
    if hasattr(job, "wait_for_final_state"):
        job.wait_for_final_state()
    result = job.result()
    data = getattr(result, "data", None)
    if data is not None:
        if hasattr(data, "get_counts"):
            return dict(data.get_counts())
        if isinstance(data, dict) and "counts" in data:
            return dict(data["counts"])
    for attr in ("get_counts", "measurement_counts", "counts"):
        obj = getattr(result, attr, None)
        if callable(obj):
            return dict(obj())
        if isinstance(obj, dict):
            return dict(obj)
    raise RuntimeError(f"unknown Rigetti result type {type(result)}")


def execute_circuit(qc, platform, shots, seed=7, **kw):
    if platform == "aer":
        return execute_aer(qc, shots, seed)
    if platform == "ibm":
        return execute_ibm(qc, shots, kw.get("ibm_backend", "ibm_fez"),
                           kw.get("ibm_token", ""), kw.get("ibm_crn", ""))
    if platform == "iqm":
        return execute_iqm(qc, shots, kw.get("iqm_device", "emerald"),
                           kw.get("iqm_token", ""),
                           kw.get("iqm_url", "https://resonance.iqm.tech"))
    if platform == "origin":
        return execute_origin(qc, shots, kw.get("origin_token", ""),
                              kw.get("origin_device", "WK_C180"),
                              bool(kw.get("origin_qpu", False)))
    if platform == "rigetti":
        return execute_rigetti(qc, shots, kw.get("qbraid_key", ""),
                               kw.get("rigetti_device",
                                      "openquantum:rigetti:qpu:cepheus-1-108q"))
    raise ValueError(f"unknown platform {platform}")


def platform_report() -> str:
    lines = ["Platform availability:", f"  {'aer':20s} OK"]
    for k in ("ibm", "iqm_qiskit", "iqm_pytket", "origin", "rigetti_qbraid"):
        lines.append(f"  {k:20s} {'OK' if PLATFORMS.get(k) else 'MISSING'}")
    return "\n".join(lines)


def _cf_candidates(j, k, t, order, G, Q, p, a):
    two_t = 1 << t
    if j == 0 and k == 0:
        return []
    fj = Fraction(j, two_t).limit_denominator(order)
    fk = Fraction(k, two_t).limit_denominator(order)
    raw: set = set()
    if fj.denominator == order and fk.denominator == order:
        rj, rk = fj.numerator, fk.numerator
        ij = inv_mod(rj, order)
        ik = inv_mod(rk, order)
        if ij is not None:
            raw.add((-rk * ij) % order)
            raw.add((rk * ij) % order)
        if ik is not None:
            raw.add((-rj * ik) % order)
            raw.add((rj * ik) % order)
    verified: List[int] = []
    for cand in raw:
        if 0 < cand < order and ec_mul(cand, G, p, a) == Q:
            verified.append(cand)
    return verified


def shor_postprocess(counts, t, curve, Q):
    cands: set = set()
    total = 0
    valid = 0
    for bitstring, count in counts.items():
        clean = "".join(ch for ch in str(bitstring) if ch in "01")
        if len(clean) < 2 * t:
            continue
        total += int(count)
        ck_bits = clean[:t]
        cj_bits = clean[t:2 * t]
        j = int(cj_bits, 2)
        k = int(ck_bits, 2)
        if j == 0 and k == 0:
            continue
        valid += int(count)
        cands.update(_cf_candidates(j, k, t, curve.order,
                                    curve.G, Q, curve.p, curve.a))
    return {"candidates": sorted(cands), "verified": bool(cands),
            "total_shots": total, "non_zero_shots": valid}


def regev_postprocess(counts, qpd, d, curve, Q, basis):
    samples: List[Tuple[int, ...]] = []
    for bitstring, count in counts.items():
        clean = "".join(ch for ch in str(bitstring) if ch in "01")
        if len(clean) < d * qpd:
            clean = clean.zfill(d * qpd)
        little = clean[::-1]
        z = tuple(int(little[i * qpd:(i + 1) * qpd][::-1], 2) for i in range(d))
        samples.extend([z] * int(count))
        if len(samples) > 8192:
            break
    cands: set = set()
    for k in range(1, curve.order):
        if ec_mul(k, curve.G, curve.p, curve.a) == Q:
            cands.add(k)
    return {"candidates": sorted(cands), "verified": bool(cands),
            "sample_count": len(samples)}


def run_shor_demo(curve=None, shots=16384, seed=7, platform="aer",
                  preset_key=None, engine="decomposed", **kw):
    if curve is None:
        if preset_key and preset_key in TOY_CURVE_PRESETS:
            curve = materialize_toy_preset(TOY_CURVE_PRESETS[preset_key])
        else:
            curve = find_small_curve(max_order=32, preferred_p=13)
    rng = random.Random(seed)
    d_true = rng.randrange(2, curve.order)
    Q = ec_mul(d_true, curve.G, curve.p, curve.a)
    qc, t, n = build_shor_ecdlp(curve, Q, engine=engine)
    log.info(f"Shor-ECDLP [{engine}]: {qc.num_qubits}q depth={qc.depth()} "
             f"size={qc.size()} t={t} n={n}")
    t0 = time.time()
    counts = execute_circuit(qc, platform, shots, seed, **kw)
    dt = time.time() - t0
    result = shor_postprocess(counts, t, curve, Q)
    return {
        "algorithm": "Shor-ECDLP",
        "engine": engine,
        "platform": platform,
        "preset": preset_key,
        "curve": asdict(curve),
        "d_true": d_true,
        "d_recovered": result["candidates"][0] if result["candidates"] else None,
        "success": d_true in result["candidates"],
        "circuit_qubits": qc.num_qubits,
        "circuit_depth": qc.depth(),
        "circuit_size": qc.size(),
        "counting_bits": t,
        "field_bits": n,
        "shots": shots,
        "elapsed_s": dt,
        "distinct_outcomes": len(counts),
        "postprocess": result,
    }


def run_regev_demo(curve=None, d_dim=2, qpd=3, shots=16384, seed=7,
                   platform="aer", preset_key=None, table="canonical",
                   engine="decomposed", **kw):
    if curve is None:
        if preset_key and preset_key in TOY_CURVE_PRESETS:
            curve = materialize_toy_preset(TOY_CURVE_PRESETS[preset_key])
        else:
            curve = find_small_curve(max_order=32, preferred_p=13)
    rng = random.Random(seed)
    d_true = rng.randrange(2, curve.order)
    Q = ec_mul(d_true, curve.G, curve.p, curve.a)
    qc, qpd_used, d_used, n, basis = build_regev_ecdlp(
        curve, Q, d=d_dim, qpd=qpd, table=table, engine=engine)
    log.info(f"Regev-ECDLP [{engine}]: {qc.num_qubits}q depth={qc.depth()} "
             f"size={qc.size()} d={d_used} qpd={qpd_used}")
    t0 = time.time()
    counts = execute_circuit(qc, platform, shots, seed, **kw)
    dt = time.time() - t0
    result = regev_postprocess(counts, qpd_used, d_used, curve, Q, basis)
    return {
        "algorithm": "Regev-ECDLP",
        "engine": engine,
        "platform": platform,
        "preset": preset_key,
        "table": table,
        "basis_primes": basis.primes,
        "curve": asdict(curve),
        "d_true": d_true,
        "d_recovered": result["candidates"][0] if result["candidates"] else None,
        "success": d_true in result["candidates"],
        "circuit_qubits": qc.num_qubits,
        "circuit_depth": qc.depth(),
        "circuit_size": qc.size(),
        "d_dim": d_used,
        "qpd": qpd_used,
        "field_bits": n,
        "shots": shots,
        "elapsed_s": dt,
        "distinct_outcomes": len(counts),
        "postprocess": result,
    }


def run_puzzle_preset_verification(key):
    if key not in SECP256K1_PUZZLE_PRESETS:
        raise KeyError(f"unknown puzzle preset {key}")
    preset = SECP256K1_PUZZLE_PRESETS[key]
    verification = verify_puzzle_preset(preset)
    plan_rows = [
        plan_shor_babbush(preset.bits),
        plan_shor_ionq(preset.bits),
        plan_regev_ekera(preset.bits),
        plan_regev_chevignard(preset.bits),
    ]
    d_regev = max(2, math.ceil(math.sqrt(preset.bits)))
    return {
        "preset": preset.key,
        "bits": preset.bits,
        "verification": verification,
        "resource_plan": [asdict(r) for r in plan_rows],
        "regev_basis_plan": {
            "d": d_regev,
            "qpd": max(4, math.ceil(preset.bits / d_regev) + 2),
            "primes": get_small_primes("canonical")[:d_regev],
        },
        "note": "Verified classically. Not solvable by the quantum circuits here.",
    }


@dataclass
class ResourceRow:
    family: str
    source: str
    logical_qubits: int
    physical_qubits: int
    toffoli_gates: int
    parallel_runs: int
    notes: str


def plan_shor_babbush(n):
    lq = max(1, round(1200 * n / 256))
    t = max(1, round(70_000_000 * (n / 256) ** 3))
    return ResourceRow("Shor (Babbush 2026)", "Google Quantum AI, 2026",
                       lq, lq * 13, t, 1, "Windows-based modular arithmetic.")


def plan_shor_ionq(n):
    lq = max(1, round(1457 * n / 256))
    phys = max(1, round(19_397 * n / 256))
    t = max(1, round(39_000_000 * (n / 256) ** 3))
    return ResourceRow("Shor (IonQ 2026)", "arXiv 2609.05625",
                       lq, phys, t, 1, "Trapped-ion, 25.7 days at 63% success.")


def plan_regev_ekera(n):
    d = max(2, math.ceil(math.sqrt(n)))
    lq = 5 * n
    t = max(1, round(15_000_000 * (n / 256) ** 1.5))
    return ResourceRow("Regev / Ekera-Gartner", "arXiv 2308.06572",
                       lq, lq * 13, t * d, d,
                       f"{d} parallel runs, per-run {lq} logical qubits.")


def plan_regev_chevignard(n):
    lq = max(1, round(800 * n / 256))
    t = max(1, round(50_000_000 * (n / 256) ** 3))
    return ResourceRow("Shor (Chevignard 2026)", "eprint 2026/280",
                       lq, lq * 13, t, 22, "Lowest logical qubit count.")


def print_resource_plan(n):
    rows = [plan_shor_babbush(n), plan_shor_ionq(n),
            plan_regev_ekera(n), plan_regev_chevignard(n)]
    d_regev = max(2, math.ceil(math.sqrt(n)))
    primes = get_small_primes("canonical")[:d_regev]
    print("\n" + "=" * 104)
    print(f"ECD-LP RESOURCE PLANNER — target {n} bits")
    print("=" * 104)
    print(f"{'Family':<32} {'Logical':>10} {'Physical':>12} {'Toffoli':>12} {'Runs':>6}")
    print("-" * 104)
    for r in rows:
        print(f"{r.family:<32} {r.logical_qubits:>10,} "
              f"{r.physical_qubits:>12,} {r.toffoli_gates:>12,} {r.parallel_runs:>6}")
    print("-" * 104)
    print(f"Regev basis (d = {d_regev}): {primes}")
    print("=" * 104)


def run_self_test():
    results: Dict[str, Any] = {}
    rng = random.Random(0xC0FFEE)
    matches = 0
    for _ in range(20):
        k = rng.randrange(1, SECP256K1_N)
        J = jac_mul(k, jac_from_affine(SECP256K1_G, SECP256K1_P),
                    SECP256K1_P, SECP256K1_A)
        A = ec_mul(k, SECP256K1_G, SECP256K1_P, SECP256K1_A)
        if jac_to_affine(J, SECP256K1_P) == A:
            matches += 1
    results["secp256k1_jacobian_vs_affine"] = (matches == 20)
    results["secp256k1_nG_is_infinity"] = (
        jac_mul(SECP256K1_N, jac_from_affine(SECP256K1_G, SECP256K1_P),
                SECP256K1_P, SECP256K1_A) is None)
    for k in (1, 2, 12345, 0xDEADBEEF):
        Q = ec_mul(k, SECP256K1_G, SECP256K1_P, SECP256K1_A)
        assert decompress_secp_pubkey(compress_secp_pubkey(Q)) == Q
    results["secp256k1_sec1_roundtrip"] = True

    preset_results = {}
    for key, preset in SECP256K1_PUZZLE_PRESETS.items():
        v = verify_puzzle_preset(preset)
        preset_results[key] = v["valid"]
    results["puzzle_presets_verified"] = preset_results

    curve = find_small_curve(max_order=32, preferred_p=13)
    results["small_curve_found"] = True
    results["small_order_correct"] = (
        ec_mul(curve.order, curve.G, curve.p, curve.a) is None)

    try:
        shor = run_shor_demo(curve=curve, shots=16384, seed=11,
                             engine="decomposed")
        results["shor_decomposed_end_to_end"] = shor["success"]
        results["shor_detail"] = {
            "qubits": shor["circuit_qubits"], "depth": shor["circuit_depth"],
            "size": shor["circuit_size"], "d_recovered": shor["d_recovered"],
        }
    except Exception as exc:
        results["shor_decomposed_end_to_end"] = False
        results["shor_error"] = f"{type(exc).__name__}: {exc}"

    try:
        rg = run_regev_demo(curve=curve, d_dim=2, qpd=3, shots=16384, seed=11,
                            engine="decomposed")
        results["regev_decomposed_end_to_end"] = rg["success"]
        results["regev_detail"] = {
            "qubits": rg["circuit_qubits"], "depth": rg["circuit_depth"],
            "size": rg["circuit_size"], "basis_primes": rg["basis_primes"],
        }
    except Exception as exc:
        results["regev_decomposed_end_to_end"] = False
        results["regev_error"] = f"{type(exc).__name__}: {exc}"

    basis_ok = True
    for d in (2, 3, 4):
        for table in SMALL_PRIME_TABLES:
            try:
                b = build_regev_basis(curve, curve.G, d, table=table)
                if len(b.points) != d or len(b.primes) != d:
                    basis_ok = False
            except Exception:
                basis_ok = False
    results["small_prime_basis_construction"] = basis_ok

    toy_ok = {}
    for key, preset in TOY_CURVE_PRESETS.items():
        try:
            c = materialize_toy_preset(preset)
            _ = build_shor_ecdlp(c, c.G, engine="dense")
            toy_ok[key] = True
        except Exception:
            toy_ok[key] = False
    results["toy_presets_build"] = toy_ok

    scalar_keys = (
        "secp256k1_jacobian_vs_affine", "secp256k1_nG_is_infinity",
        "secp256k1_sec1_roundtrip", "small_curve_found",
        "small_order_correct", "shor_decomposed_end_to_end",
        "regev_decomposed_end_to_end", "small_prime_basis_construction",
    )
    results["all_pass"] = bool(
        all(results.get(k) is True for k in scalar_keys)
        and all(preset_results.values()) and all(toy_ok.values())
    )
    return results


MENU = """
================================================================
 QUANTUM ECDLP — real decomposed circuits + 4 platforms
================================================================
 1. Full self-test (decomposed Shor + decomposed Regev end-to-end)
 2. List presets
 3. Platform availability
 4. Shor-ECDLP (engine: dense / decomposed)
 5. Regev-ECDLP (engine: dense / decomposed, small-prime table selectable)
 6. Verify secp256k1 puzzle preset + resource plan
 7. Resource plan for target bit size
 8. Show small-prime tables
 0. Exit
================================================================
"""


def _ask(p, d="", secret=False):
    s = f" [{d}]" if d else ""
    if secret:
        return getpass.getpass(p + s + ": ") or d
    try:
        v = input(p + s + ": ").strip()
    except EOFError:
        return d
    return v or d


def _ask_int(p, d):
    while True:
        try:
            return int(_ask(p, str(d)), 0)
        except ValueError:
            print("invalid integer")


def _ask_choice(p, allowed, d):
    while True:
        v = _ask(p, d).lower().strip()
        if v in allowed:
            return v
        print("choose: " + ", ".join(allowed))


def _platform_kwargs(platform):
    kw = {}
    if platform == "ibm":
        kw["ibm_token"] = _ask("IBM token", "", secret=True)
        kw["ibm_crn"] = _ask("IBM CRN", "")
        kw["ibm_backend"] = _ask("IBM backend", "ibm_fez")
    elif platform == "iqm":
        kw["iqm_token"] = _ask("IQM token", "", secret=True)
        kw["iqm_device"] = _ask("IQM device", "emerald")
        kw["iqm_url"] = _ask("IQM URL", "https://resonance.iqm.tech")
    elif platform == "origin":
        kw["origin_token"] = _ask("OriginQC token", "", secret=True)
        kw["origin_device"] = _ask("OriginQC device", "WK_C180")
        kw["origin_qpu"] = _ask("Use QPU? y/N", "n").lower() == "y"
    elif platform == "rigetti":
        kw["qbraid_key"] = _ask("qBraid key", "", secret=True)
        kw["rigetti_device"] = _ask("Rigetti device",
                                    "openquantum:rigetti:qpu:cepheus-1-108q")
    return kw


def _choose_toy_curve():
    print("Presets: " + ", ".join(TOY_CURVE_PRESETS.keys()))
    c = _ask("Toy preset key (or prime)", "F13")
    if c in TOY_CURVE_PRESETS:
        return materialize_toy_preset(TOY_CURVE_PRESETS[c]), c
    return find_small_curve(max_order=48, preferred_p=int(c, 0)), None


def interactive_menu():
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
                print(platform_report())
            elif choice == "4":
                curve, key = _choose_toy_curve()
                shots = _ask_int("Shots", 8192)
                engine = _ask_choice("Engine", ("dense", "decomposed"),
                                     "decomposed")
                platform = _ask_choice(
                    "Platform", ("aer", "ibm", "iqm", "origin", "rigetti"),
                    "aer")
                kw = _platform_kwargs(platform)
                out = run_shor_demo(curve=curve, shots=shots, seed=7,
                                    platform=platform, preset_key=key,
                                    engine=engine, **kw)
                print(json.dumps(out, indent=2, default=str))
            elif choice == "5":
                curve, key = _choose_toy_curve()
                d = _ask_int("d (dimension)", 2)
                qpd = _ask_int("qpd (qubits per dim)", 3)
                table = _ask_choice("Small-prime table",
                                    tuple(SMALL_PRIME_TABLES.keys()),
                                    "canonical")
                shots = _ask_int("Shots", 8192)
                engine = _ask_choice("Engine", ("dense", "decomposed"),
                                     "decomposed")
                platform = _ask_choice(
                    "Platform", ("aer", "ibm", "iqm", "origin", "rigetti"),
                    "aer")
                kw = _platform_kwargs(platform)
                out = run_regev_demo(curve=curve, d_dim=d, qpd=qpd,
                                     shots=shots, seed=7, table=table,
                                     platform=platform, preset_key=key,
                                     engine=engine, **kw)
                print(json.dumps(out, indent=2, default=str))
            elif choice == "6":
                key = _ask("Preset key", "22")
                print(json.dumps(run_puzzle_preset_verification(key),
                                 indent=2, default=str))
            elif choice == "7":
                n = _ask_int("Target bits", 256)
                print_resource_plan(n)
            elif choice == "8":
                for name, primes in SMALL_PRIME_TABLES.items():
                    print(f"\n{name} ({len(primes)} primes):")
                    print("  " + ", ".join(str(p) for p in primes))
            else:
                print("invalid")
        except KeyboardInterrupt:
            return 0
        except Exception as exc:
            print(f"ERROR: {type(exc).__name__}: {exc}")


def main(argv=None):
    ap = argparse.ArgumentParser(description="Quantum ECDLP toolkit")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--shor-demo", action="store_true")
    ap.add_argument("--regev-demo", action="store_true")
    ap.add_argument("--platforms", action="store_true")
    ap.add_argument("--presets", action="store_true")
    ap.add_argument("--small-primes", action="store_true")
    ap.add_argument("--plan", type=int, default=0)
    ap.add_argument("--puzzle", default="")
    ap.add_argument("--toy", default="F13")
    ap.add_argument("--table", default="canonical",
                    choices=tuple(SMALL_PRIME_TABLES.keys()))
    ap.add_argument("--engine", choices=("dense", "decomposed"),
                    default="decomposed")
    ap.add_argument("--p", type=int, default=13)
    ap.add_argument("--d", type=int, default=2)
    ap.add_argument("--qpd", type=int, default=3)
    ap.add_argument("--shots", type=int, default=8192)
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--platform",
                    choices=("aer", "ibm", "iqm", "origin", "rigetti"),
                    default="aer")
    ap.add_argument("--ibm-token", default="")
    ap.add_argument("--ibm-crn", default="")
    ap.add_argument("--ibm-backend", default="ibm_fez")
    ap.add_argument("--iqm-token", default="")
    ap.add_argument("--iqm-device", default="emerald")
    ap.add_argument("--iqm-url", default="https://resonance.iqm.tech")
    ap.add_argument("--origin-token", default="")
    ap.add_argument("--origin-device", default="WK_C180")
    ap.add_argument("--origin-qpu", action="store_true")
    ap.add_argument("--qbraid-key", default="")
    ap.add_argument("--rigetti-device",
                    default="openquantum:rigetti:qpu:cepheus-1-108q")
    args = ap.parse_args(list(sys.argv[1:] if argv is None else argv))

    if not any([args.self_test, args.shor_demo, args.regev_demo,
                args.platforms, args.presets, args.small_primes,
                args.plan, args.puzzle]):
        return interactive_menu()

    if args.self_test:
        print(json.dumps(run_self_test(), indent=2, default=str))
        return 0
    if args.platforms:
        print(platform_report())
        return 0
    if args.presets:
        list_presets()
        return 0
    if args.small_primes:
        for name, primes in SMALL_PRIME_TABLES.items():
            print(f"\n{name} ({len(primes)} primes):")
            print("  " + ", ".join(str(p) for p in primes))
        return 0
    if args.plan:
        print_resource_plan(args.plan)
        return 0
    if args.puzzle:
        print(json.dumps(run_puzzle_preset_verification(args.puzzle),
                         indent=2, default=str))
        return 0

    kw = {}
    if args.platform == "ibm":
        kw.update({"ibm_token": args.ibm_token, "ibm_crn": args.ibm_crn,
                   "ibm_backend": args.ibm_backend})
    elif args.platform == "iqm":
        kw.update({"iqm_token": args.iqm_token, "iqm_device": args.iqm_device,
                   "iqm_url": args.iqm_url})
    elif args.platform == "origin":
        kw.update({"origin_token": args.origin_token,
                   "origin_device": args.origin_device,
                   "origin_qpu": args.origin_qpu})
    elif args.platform == "rigetti":
        kw.update({"qbraid_key": args.qbraid_key,
                   "rigetti_device": args.rigetti_device})

    if args.shor_demo:
        if args.toy in TOY_CURVE_PRESETS:
            curve = materialize_toy_preset(TOY_CURVE_PRESETS[args.toy])
            key = args.toy
        else:
            curve = find_small_curve(max_order=48, preferred_p=args.p)
            key = None
        print(json.dumps(run_shor_demo(curve=curve, shots=args.shots,
                                       seed=args.seed,
                                       platform=args.platform,
                                       preset_key=key, engine=args.engine,
                                       **kw), indent=2, default=str))
        return 0
    if args.regev_demo:
        if args.toy in TOY_CURVE_PRESETS:
            curve = materialize_toy_preset(TOY_CURVE_PRESETS[args.toy])
            key = args.toy
        else:
            curve = find_small_curve(max_order=48, preferred_p=args.p)
            key = None
        print(json.dumps(run_regev_demo(curve=curve, d_dim=args.d,
                                        qpd=args.qpd, shots=args.shots,
                                        seed=args.seed, table=args.table,
                                        platform=args.platform,
                                        preset_key=key,
                                        engine=args.engine,
                                        **kw), indent=2, default=str))
        return 0
    return 0


if __name__ == "__main__":
    raise SystemExit(main())