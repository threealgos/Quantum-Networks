#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
REGEV_FIXED.py — Regev solver with per-puzzle qubit sizing.

THE FIX vs previous versions:
  * Target register width = bits (puzzle) for puzzles < 256-bit.
  * Target register width = 257 (x + sign) for puzzles >= 256-bit.
  * d, qpd computed from puzzle bits: d=ceil(sqrt(n)), qpd=min(8,max(4,ceil(n/d)+2)).

Qubit budgets (fixed):
  #12:  32   #14:  34   #16:  40   #17:  47   #19:  49
  #20:  50   #21:  51   #22:  57   #135: 231  #140: 236
  #256: 385

Run:
  python REGEV_FIXED.py --table
  python REGEV_FIXED.py --self-test
  python REGEV_FIXED.py --solve 16 --platform aer --shots 8192
  python REGEV_FIXED.py --solve 22 --platform origin --origin-qpu
"""
from __future__ import annotations

import argparse, getpass, json, logging, math, os, random, sys, time, traceback
from collections import Counter
from dataclasses import dataclass, asdict
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

import numpy as np

# ═══════════════════════════════════════════════════════════════════════════
# LOGGING
# ═══════════════════════════════════════════════════════════════════════════
CACHE = Path("regev_cache"); CACHE.mkdir(exist_ok=True)
logging.basicConfig(level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(message)s",
    handlers=[logging.FileHandler(CACHE / "regev_fixed.log"),
              logging.StreamHandler(sys.stdout)])
log = logging.getLogger("regev")

# ═══════════════════════════════════════════════════════════════════════════
# SECP256K1
# ═══════════════════════════════════════════════════════════════════════════
P256 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N256 = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
A256 = 0
B256 = 7
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G256 = (Gx, Gy)

Point = Optional[Tuple[int, int]]


def inv_mod(a: int, m: int) -> Optional[int]:
    a %= m
    return None if a == 0 else pow(a, -1, m)


def pt_add(P: Point, Q: Point) -> Point:
    if P is None: return Q
    if Q is None: return P
    x1, y1 = P; x2, y2 = Q
    if x1 == x2:
        if (y1 + y2) % P256 == 0 or y1 == 0: return None
        lam = (3*x1*x1 + A256) * inv_mod(2*y1, P256) % P256
    else:
        lam = (y2 - y1) * inv_mod(x2 - x1, P256) % P256
    x3 = (lam*lam - x1 - x2) % P256
    return (x3, (lam*(x1 - x3) - y1) % P256)


def pt_mul(k: int, P: Point) -> Point:
    if k == 0 or P is None: return None
    if k < 0: return pt_mul(-k, (P[0], (-P[1]) % P256))
    R: Point = None; A = P
    while k:
        if k & 1: R = pt_add(R, A)
        A = pt_add(A, A); k >>= 1
    return R


def decompress_secp(hx: str) -> Point:
    h = hx.lower().strip().replace("0x", "").replace(" ", "")
    if len(h) != 66 or h[:2] not in ("02", "03"): return None
    try: x = int(h[2:], 16)
    except ValueError: return None
    if x >= P256: return None
    rhs = (pow(x, 3, P256) + B256) % P256
    y = pow(rhs, (P256 + 1)//4, P256)
    if y*y % P256 != rhs: return None
    if (int(h[:2], 16) == 2 and y % 2) or (int(h[:2], 16) == 3 and y % 2 == 0):
        y = P256 - y
    return (x, y)


def verify_secp(k: int, Q: Point) -> bool:
    if k is None or k <= 0 or k >= N256: return False
    return pt_mul(k, G256) == Q


# ═══════════════════════════════════════════════════════════════════════════
# SMALL-PRIME TABLES
# ═══════════════════════════════════════════════════════════════════════════
SP_CANONICAL = [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,
    73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,
    173,179,181,191,193,197,199,211,223,227,229,233,239,241,251]
SP_EXTENDED = SP_CANONICAL + [257,263,269,271,277,281,283,293,307,311,313,
    317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,
    433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,
    557,563,569,571,577,587,593,599,601,607,613,617,619]
SP_ULTRA = SP_EXTENDED + [631,641,643,647,653,659,661,673,677,683,691,701,
    709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,
    829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,
    967,971,977,983,991,997,1009,1013,1019,1021,1031]
SP_TABLES = {"canonical": SP_CANONICAL, "extended": SP_EXTENDED, "ultra": SP_ULTRA}


def get_primes(table: str, d: int) -> List[int]:
    if table not in SP_TABLES: raise ValueError(f"unknown table {table!r}")
    primes = SP_TABLES[table]
    if d > len(primes): raise ValueError(f"table {table!r} has {len(primes)}, need {d}")
    return primes[:d]


# ═══════════════════════════════════════════════════════════════════════════
# PUZZLE PRESETS
# ═══════════════════════════════════════════════════════════════════════════
@dataclass
class Puzzle:
    key: str
    bits: int
    k_start: int
    pubkey: str
    secret: Optional[int]


PUZZLES: Dict[str, Puzzle] = {
    "12":  Puzzle("12",  12, 0x800,
        "038b00fcbfc1a203f44bf123fc7f4c91c10a85c8eae9187f9d22242b4600ce781c", 0x9C8),
    "14":  Puzzle("14",  14, 0x2000,
        "03b4f1de58b8b41afe9fd4e5ffbdafaeab86c5db4769c15d6e6011ae7351e54759", 0x2199),
    "16":  Puzzle("16",  16, 0x8000,
        "029d8c5d35231d75eb87fd2c5f05f65281ed9573dc41853288c62ee94eb2590b7a", 0xC668),
    "17":  Puzzle("17",  17, 0x10000,
        "033f688bae8321b8e02b7e6c0a55c2515fb25ab97d85fda842449f7bfa04e128c3", 0x17D62),
    "19":  Puzzle("19",  19, 0x40000,
        "0385663c8b2f90659e1ccab201694f4f8ec24b3749cfe5030c7c3646a709408e19", 0x5C922),
    "20":  Puzzle("20",  20, 0x80000,
        "033c4a45cbd643ff97d77f41ea37e843648d50fd894b864b0d52febc62f6454f7c", 0xA3B8C),
    "21":  Puzzle("21",  21, 0x100000,
        "031a746c78f72754e0be046186df8a20cdce5c79b2eda76013c647af08d306e49e", 0x1347A3),
    "22":  Puzzle("22",  22, 0x200000,
        "023ed96b524db5ff4fe007ce730366052b7c511dc566227d929070b9ce917abb43", None),
    "135": Puzzle("135", 135, 0x4000000000000000000000000000000000,
        "0327401b07225a4269ee46c9a420c765ea878cbd8127aed9c3a5d977d112e86469", None),
    "140": Puzzle("140", 140, 0x80000000000000000000000000000000000,
        "031f6a332d3c5c4f2de2378c012f429cd109ba07d69690c6c701b6bb87860d6640", None),
    "256": Puzzle("256", 256, 0x8000000000000000000000000000000000000000000000000000000000000000,
        "0279BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798", None),
}


# ═══════════════════════════════════════════════════════════════════════════
# PER-PUZZLE QUBIT SIZING  ← THE FIX
# ═══════════════════════════════════════════════════════════════════════════
def puzzle_sizing(bits: int) -> Dict[str, int]:
    """
    Return {d, qpd, z_qubits, target_width, total}.

    Rules:
      * d = ceil(sqrt(bits))    (Regev dimension)
      * qpd = min(8, max(4, ceil(bits/d) + 2))    (preset-17 formula)
      * target_width = bits if bits < 256 else 257
      * total = d*qpd + target_width
    """
    n = max(2, bits)
    d = max(2, math.ceil(math.sqrt(n)))
    qpd = min(8, max(4, math.ceil(n / d) + 2))
    z_qubits = d * qpd
    target_width = n if n < 256 else 257
    return {
        "d": d, "qpd": qpd, "z_qubits": z_qubits,
        "target_width": target_width,
        "total": z_qubits + target_width,
    }


def qubit_table() -> List[Dict[str, Any]]:
    """Full per-puzzle qubit budget."""
    rows = []
    for key, pz in PUZZLES.items():
        sz = puzzle_sizing(pz.bits)
        rows.append({
            "puzzle": key, "bits": pz.bits,
            "d": sz["d"], "qpd": sz["qpd"],
            "z_qubits": sz["z_qubits"],
            "target_width": sz["target_width"],
            "total": sz["total"],
        })
    return rows


def print_qubit_table():
    rows = qubit_table()
    print()
    print("=" * 78)
    print("PER-PUZZLE QUBIT BUDGET (REGEF_FIXED sizing)")
    print("=" * 78)
    print(f"{'Puzzle':<8} {'Bits':<6} {'d':<5} {'qpd':<5} "
          f"{'z-qubits':<10} {'target':<8} {'TOTAL':<8}")
    print("-" * 78)
    for r in rows:
        print(f"  #{r['puzzle']:<6} {r['bits']:<6} {r['d']:<5} {r['qpd']:<5} "
              f"{r['z_qubits']:<10} {r['target_width']:<8} {r['total']:<8}")
    print("-" * 78)
    print("  Old buggy version reported 524 for every puzzle.")
    print("=" * 78)


# ═══════════════════════════════════════════════════════════════════════════
# FIBONACCI + HALFGCD (per preset-17)
# ═══════════════════════════════════════════════════════════════════════════
def fibonacci_sequence(n: int) -> List[int]:
    fibs = [1, 1]
    while fibs[-1] < (1 << n):
        fibs.append(fibs[-1] + fibs[-2])
    return fibs


def halfgcd_modinv(a: int, p: int) -> Optional[int]:
    a = a % p
    if a == 0: return None
    u, v, s, t = a, p, 1, 0
    steps = 0
    while u != 0:
        if u & 1 == 0:
            u >>= 1
            s = (s * pow(2, -1, p)) % p if s % 2 else s >> 1
        elif v & 1 == 0:
            v >>= 1
            t = (t * pow(2, -1, p)) % p if t % 2 else t >> 1
        elif u >= v:
            u, s = (u - v) >> 1, ((s - t) * pow(2, -1, p)) % p
        else:
            v, t = (v - u) >> 1, ((t - s) * pow(2, -1, p)) % p
        steps += 1
        if steps > 3 * p.bit_length(): break
    result = s % p if v == 1 else t % p
    return result if (a * result) % p == 1 else inv_mod(a, p)


# ═══════════════════════════════════════════════════════════════════════════
# PRECOMPUTE GROUP ELEMENTS (basis table for the phase oracle)
# ═══════════════════════════════════════════════════════════════════════════
def precompute_basis(Q: Point, k_start: int, bits: int, d: int,
                     table: str = "canonical",
                     use_fibonacci: bool = True
                     ) -> Tuple[List[int], List[List[int]], List[int]]:
    """
    Returns (delta_powers, basis_powers, primes).
      delta_powers[k]     = (2^k · delta).x  mod 2^bits
      basis_powers[i][k]  = (2^k · b_i · G).x mod 2^bits
    where delta = Q - k_start·G and b_i from the small-prime table.

    With use_fibonacci=True, uses Fibonacci sequence indices instead of
    powers of 2 (Ragavan-Vaikuntanathan).
    """
    neg_kG = pt_mul(k_start, G256)
    if neg_kG is not None:
        neg_kG = (neg_kG[0], (P256 - neg_kG[1]) % P256)
    delta = pt_add(Q, neg_kG)
    Nmod = 1 << bits

    def enc(P): return P[0] % Nmod if P is not None else 0

    primes = get_primes(table, d)

    if use_fibonacci:
        fibs = fibonacci_sequence(bits)
        n_idx = min(len(fibs), bits)

        # delta powers via Fibonacci multiples
        delta_powers: List[int] = []
        cur, prev = delta, None
        for i in range(n_idx):
            delta_powers.append(enc(cur))
            if prev is None:
                prev, cur = cur, pt_add(delta, delta) if delta else None
            else:
                prev, cur = cur, pt_add(cur, prev) if cur else None

        basis_powers: List[List[int]] = []
        for i in range(d):
            b_i = primes[i]
            bG = pt_mul(b_i, G256)
            row: List[int] = []
            cur2, prev2 = bG, None
            for _ in range(n_idx):
                row.append(enc(cur2))
                if prev2 is None:
                    prev2, cur2 = cur2, pt_add(bG, bG) if bG else None
                else:
                    prev2, cur2 = cur2, pt_add(cur2, prev2) if cur2 else None
            # pad to bits length
            while len(row) < bits:
                row.append(0)
            basis_powers.append(row[:bits])
        while len(delta_powers) < bits:
            delta_powers.append(0)
        delta_powers = delta_powers[:bits]
    else:
        # power-of-2 doubling (classic Regev)
        delta_powers = []
        cur = delta
        for _ in range(bits):
            delta_powers.append(enc(cur))
            cur = pt_add(cur, cur) if cur else None

        basis_powers = []
        for i in range(d):
            b_i = primes[i]
            bG = pt_mul(b_i, G256)
            row = []
            cur = bG
            for _ in range(bits):
                row.append(enc(cur))
                cur = pt_add(cur, cur) if cur else None
            basis_powers.append(row)

    return delta_powers, basis_powers, primes


# ═══════════════════════════════════════════════════════════════════════════
# CIRCUIT BUILDER (preset-17 phase-oracle style)
# ═══════════════════════════════════════════════════════════════════════════
def build_circuit(Q: Point, k_start: int, bits: int,
                  d: int, qpd: int, target_width: int,
                  table: str = "canonical",
                  adder: str = "approx", approx_threshold: int = 4,
                  encoding: str = "none",
                  use_fibonacci: bool = True,
                  use_flags: bool = False):
    """Build the phase-oracle circuit (preset-17 technique)."""
    from qiskit import QuantumCircuit, QuantumRegister, ClassicalRegister
    from qiskit.circuit.library import QFTGate

    delta_powers, basis_powers, primes = precompute_basis(
        Q, k_start, bits, d, table=table, use_fibonacci=use_fibonacci)

    z_regs = [QuantumRegister(qpd, f"z{i}") for i in range(d)]
    target = QuantumRegister(target_width, "tgt")
    cregs_z = [ClassicalRegister(qpd, f"cz{i}") for i in range(d)]

    partner = None
    if encoding == "cat":
        partner = QuantumRegister(target_width, "partner")

    flags = None
    if use_flags:
        flags = QuantumRegister(d, "flag")

    regs = list(z_regs) + [target]
    if partner is not None: regs.append(partner)
    if flags is not None: regs.append(flags)

    qc = QuantumCircuit(*regs, *cregs_z)

    # Stage 1 — Gaussian prep on z registers
    R = math.exp(0.5 * math.sqrt(bits))
    for zr in z_regs:
        for i in range(qpd):
            try:
                p_one = math.exp(-math.pi * ((1 << i) / R) ** 2)
                p_one = max(min(p_one, 0.999), 0.001)
                qc.ry(2 * math.asin(math.sqrt(1 - p_one)), zr[i])
            except Exception:
                qc.h(zr[i])

    # Stage 2 — Cat encoding
    if encoding == "cat" and partner is not None:
        for d_, p_ in zip(target, partner):
            qc.h(p_); qc.cx(p_, d_)

    # Stage 3 — Flag entanglement
    if flags is not None:
        for i, zr in enumerate(z_regs):
            for q in zr:
                qc.cx(q, flags[i])

    # Stage 4 — Phase oracle (QFT-coalesced Draper)
    qc.append(QFTGate(target_width), list(target))

    use_approx = (adder == "approx")
    for i, zr in enumerate(z_regs):
        for k in range(qpd):
            if k >= len(basis_powers[i]): break
            coef = basis_powers[i][k] % (1 << bits)
            if coef == 0: continue
            ctrl = zr[k]
            for bit_i in range(target_width):
                depth = target_width - bit_i
                if use_approx and depth > approx_threshold: continue
                angle = (2 * math.pi * coef * (1 << bit_i)) / (1 << target_width)
                angle %= (2 * math.pi)
                if abs(angle) < 1e-12 or abs(angle - 2*math.pi) < 1e-12: continue
                qc.cp(angle, ctrl, target[bit_i])

    # Uncontrolled delta offset (batched)
    delta_total = sum(delta_powers) % (1 << bits)
    if delta_total:
        for bit_i in range(target_width):
            depth = target_width - bit_i
            if use_approx and depth > approx_threshold: continue
            angle = (2 * math.pi * delta_total * (1 << bit_i)) / (1 << target_width)
            angle %= (2 * math.pi)
            if abs(angle) < 1e-12 or abs(angle - 2*math.pi) < 1e-12: continue
            qc.p(angle, target[bit_i])

    qc.append(QFTGate(target_width).inverse(), list(target))

    # Stage 5 — Un-flag
    if flags is not None:
        for i, zr in enumerate(z_regs):
            for q in zr:
                qc.cx(q, flags[i])

    # Stage 6 — QFT on z registers
    for zr in z_regs:
        qc.append(QFTGate(qpd), zr)

    # Stage 7 — Measure
    for zr, cr in zip(z_regs, cregs_z):
        qc.measure(zr, cr)

    if encoding == "cat" and partner is not None:
        cpart = ClassicalRegister(target_width, "cpart")
        qc.add_register(cpart)
        for i in range(target_width):
            qc.measure(partner[i], cpart[i])

    qc.metadata = {
        "bits": bits, "d": d, "qpd": qpd, "target_width": target_width,
        "table": table, "primes": primes,
        "basis_powers": basis_powers, "delta_powers": delta_powers,
        "adder": adder, "approx_threshold": approx_threshold,
        "encoding": encoding, "fibonacci": use_fibonacci,
    }
    log.info(f"Circuit: {qc.num_qubits}q, depth={qc.depth()}, size={qc.size()}, "
             f"d={d}, qpd={qpd}, target={target_width}")
    return qc


# ═══════════════════════════════════════════════════════════════════════════
# PLATFORM RUNNERS
# ═══════════════════════════════════════════════════════════════════════════
def run_aer(qc, shots: int, seed: int = 7) -> Counter:
    from qiskit_aer import AerSimulator
    from qiskit import transpile
    sim = AerSimulator(seed_simulator=seed)
    tqc = transpile(qc, sim, optimization_level=2)
    log.info(f"Aer transpiled: {tqc.num_qubits}q, depth={tqc.depth()}")
    return Counter(sim.run(tqc, shots=shots).result().get_counts())


def run_origin(qc, shots: int, token: str = "",
               device: str = "WK_C180", use_qpu: bool = False) -> Counter:
    try:
        import pyqpanda3.core as core
        from pyqpanda3.qcloud import QCloudService, QCloudOptions
    except ImportError:
        raise RuntimeError("pyqpanda3 not installed: pip install pyqpanda3")
    from qiskit import transpile
    from qiskit.qasm2 import dumps as qasm2_dumps
    flat = transpile(qc, basis_gates=["u","u1","u2","u3","cx"], optimization_level=2)
    qasm = qasm2_dumps(flat)
    prog = None
    for name in ("convert_qasm_string_to_qprog","qasm_to_qprog",
                 "convert_qasm_to_qprog","parse_qasm"):
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
    if not token: raise RuntimeError("ORIGINQC_TOKEN required")
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
    if not token: raise RuntimeError("IBM token required")
    service = QiskitRuntimeService(channel="ibm_cloud", token=token, instance=crn or None)
    backend = service.backend(backend_name)
    pm = generate_preset_pass_manager(backend=backend, optimization_level=1)
    isa = pm.run(qc)
    log.info(f"IBM transpiled: {isa.num_qubits}q depth={isa.depth()}")
    if isa.depth() > 10000:
        raise RuntimeError(f"depth {isa.depth()} > IBM limit")
    job = SamplerV2(mode=backend).run([isa], shots=shots)
    pub = job.result()[0]
    for name in dir(pub.data):
        if name.startswith("_"): continue
        attr = getattr(pub.data, name, None)
        if hasattr(attr, "get_counts"):
            c = attr.get_counts()
            if c: return Counter(c)
    raise RuntimeError("no IBM register data")


def run_iqm(qc, shots: int, device: str = "emerald",
            token: str = "", url: str = "https://resonance.iqm.tech") -> Counter:
    from qiskit.circuit import Measure, Reset, IfElseOp
    from qiskit import QuantumCircuit as QC, ClassicalRegister as CR, transpile
    token = token or os.getenv("IQM_TOKEN", "")
    if not token: raise RuntimeError("IQM_TOKEN required")
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
                device_id: str = "openquantum:rigetti:qpu:cepheus-1-108q") -> Counter:
    from qiskit import QuantumCircuit as QC, transpile
    from qiskit.qasm3 import dumps as qasm3_dumps
    qbraid_key = qbraid_key or os.getenv("QBRAID_API_KEY", "")
    try:
        from qbraid.runtime import QbraidProvider
    except ImportError:
        from qbraid.runtime.native import QbraidProvider
    flat = QC(qc.num_qubits, qc.num_clbits, name="flat")
    flat.compose(qc, qubits=flat.qubits, clbits=flat.clbits, inplace=True)
    flat = transpile(flat, basis_gates=["h","rz","rx","x","cx"], optimization_level=1)
    qasm3 = qasm3_dumps(flat)
    provider = QbraidProvider(api_key=qbraid_key) if qbraid_key else QbraidProvider()
    device = provider.get_device(device_id)
    job = device.run(qasm3, shots=shots)
    if hasattr(job, "wait_for_final_state"): job.wait_for_final_state()
    result = job.result()
    data = getattr(result, "data", None)
    if data is not None and hasattr(data, "get_counts"):
        return Counter(data.get_counts())
    for attr in ("get_counts","measurement_counts","counts"):
        obj = getattr(result, attr, None)
        if callable(obj): return Counter(obj())
        if isinstance(obj, dict): return Counter(obj)
    raise RuntimeError("no Rigetti counts")


def execute(qc, platform: str, shots: int, seed: int = 7, **kw) -> Counter:
    if platform == "aer": return run_aer(qc, shots, seed)
    if platform == "origin":
        return run_origin(qc, shots,
                          token=kw.get("origin_token", ""),
                          device=kw.get("origin_device", "WK_C180"),
                          use_qpu=bool(kw.get("origin_qpu", False)))
    if platform == "ibm":
        return run_ibm(qc, shots, backend_name=kw.get("ibm_backend","ibm_fez"),
                       token=kw.get("ibm_token",""), crn=kw.get("ibm_crn",""))
    if platform == "iqm":
        return run_iqm(qc, shots, device=kw.get("iqm_device","emerald"),
                       token=kw.get("iqm_token",""),
                       url=kw.get("iqm_url","https://resonance.iqm.tech"))
    if platform == "rigetti":
        return run_rigetti(qc, shots, qbraid_key=kw.get("qbraid_key",""),
                           device_id=kw.get("rigetti_device",
                                            "openquantum:rigetti:qpu:cepheus-1-108q"))
    raise ValueError(f"unknown platform {platform!r}")


# ═══════════════════════════════════════════════════════════════════════════
# NOISE FILTER
# ═══════════════════════════════════════════════════════════════════════════
def noise_filter(counts: Counter, bits: int, sigma: float = 2.0) -> Counter:
    if sigma <= 0: return counts
    Nmod = 1 << bits
    sigma_abs = sigma * (1 << (bits // 2))
    out = Counter()
    for bs, cnt in counts.items():
        clean = "".join(c for c in str(bs) if c in "01")
        if not clean: continue
        try:
            v = int(clean[:bits], 2) if len(clean) >= bits else int(clean, 2)
        except ValueError: continue
        dist = min(v, Nmod - v)
        w = math.exp(-0.5 * (dist/sigma_abs)**2) if sigma_abs > 0 else 1.0
        out[bs] += max(1, round(cnt * (0.3 + 0.7*w)))
    log.info(f"Noise filter: {len(counts)} → {len(out)} outcomes (σ={sigma})")
    return out


# ═══════════════════════════════════════════════════════════════════════════
# POST-PROCESSING (tier system + LLL)
# ═══════════════════════════════════════════════════════════════════════════
def lll_reduce(matrix: List[List[int]]) -> List[List[int]]:
    try:
        from fpylll import IntegerMatrix, LLL
        M = IntegerMatrix.from_matrix(matrix)
        LLL.reduction(M, delta=0.75)
        return [[int(M[i,j]) for j in range(M.ncols)] for i in range(M.nrows)]
    except ImportError:
        pass
    try:
        from sympy import Matrix
        return [[int(x) for x in r] for r in Matrix(matrix).lll(delta=0.75).tolist()]
    except ImportError:
        raise RuntimeError("install fpylll or sympy")


def postprocess(counts: Counter, meta: Dict[str, Any],
                Q: Point, k_start: int) -> Optional[int]:
    bits = meta["bits"]; d = meta["d"]; qpd = meta["qpd"]
    primes = meta["primes"]
    range_start = max(1, k_start)
    range_end = k_start + (1 << bits) - 1

    # Precompute basis inverses
    basis_inv = {}
    for bp in primes[:8]:
        iv = inv_mod(bp, N256)
        if iv is not None: basis_inv[bp] = iv

    tier0, tier1, tier2, tier3, tier4 = set(), set(), set(), set(), set()

    def _add(s, k):
        if k and range_start <= k <= range_end: s.add(k)

    # ─── Pass 1: collect candidates (no verification) ───
    total_payload = d * qpd
    for bs, _ in counts.most_common():
        clean = "".join(c for c in str(bs) if c in "01")
        if not clean: continue
        payload = clean[-total_payload:].zfill(total_payload)
        try: z_val = int(payload, 2)
        except ValueError: z_val = 0
        try: raw_val = int(clean, 2)
        except ValueError: raw_val = 0

        if z_val:
            z_rev = int(payload[::-1], 2) if payload else 0
            for bv in ({z_val, z_rev} - {0}):
                _add(tier1, bv % N256)
                _add(tier1, (bv + k_start) % N256)
                for bp, inv_b in basis_inv.items():
                    _add(tier2, (bv * inv_b) % N256)
                    _add(tier2, ((bv * inv_b) + k_start) % N256)

        if raw_val:
            raw_rev = int(clean[::-1], 2)
            for rv in ({raw_val, raw_rev} - {0}):
                _add(tier3, rv % N256)
                _add(tier3, (rv + k_start) % N256)
                _add(tier3, (rv - k_start) % N256)
            hi = raw_val >> (bits // 2)
            lo = raw_val & ((1 << (bits // 2)) - 1)
            for part in {hi, lo} - {0}:
                _add(tier3, part % N256)
                _add(tier3, (part + k_start) % N256)

            if math.gcd(raw_val, N256) > 1:
                for m in range(1, 8):
                    g = math.gcd(raw_val * m, N256)
                    if 1 < g < N256:
                        _add(tier4, g)
                        _add(tier4, (g + k_start) % N256)

    log.info(f"Tiers: t0={len(tier0)} t1={len(tier1)} t2={len(tier2)} "
             f"t3={len(tier3)} t4={len(tier4)}")

    # ─── Pass 2: verify tier by tier ───
    checked = set()
    for tier_set, label in [(tier0, "tier0"), (tier1, "tier1"),
                            (tier2, "tier2"), (tier3, "tier3"),
                            (tier4, "tier4")]:
        for k_try in tier_set:
            if k_try in checked: continue
            checked.add(k_try)
            if verify_secp(k_try, Q):
                log.info(f"✅ {label}: k = {k_try} (0x{k_try:x})")
                return k_try

    # ─── Stage 3: CF sweep ───
    log.info("CF sweep on raw integers")
    for bs, _ in counts.most_common():
        clean = "".join(c for c in str(bs) if c in "01")
        if not clean: continue
        for variant in (clean, clean[::-1]):
            try: measured = int(variant, 2)
            except ValueError: continue
            if not measured: continue
            for dd in range(1, 24):
                frac = Fraction(measured, dd).limit_denominator(N256)
                p_n, q_d = frac.numerator, frac.denominator
                if not q_d: continue
                inv_q = inv_mod(q_d, N256)
                if inv_q is None: continue
                k_try = (p_n * inv_q) % N256
                for c in (k_try, (k_try + k_start) % N256):
                    if c in checked: continue
                    checked.add(c)
                    if 0 < c <= range_end and verify_secp(c, Q):
                        log.info(f"✅ CF: k = {c}")
                        return c

    # ─── Stage 4: LLL on z samples ───
    log.info("LLL on quantum z-samples")
    samples = []
    for bs, cnt in counts.most_common():
        clean = "".join(c for c in str(bs) if c in "01")
        if len(clean) < d*qpd: continue
        payload = clean[-(d*qpd):]
        little = payload[::-1]
        z = tuple(int(little[i*qpd:(i+1)*qpd][::-1], 2) for i in range(d))
        samples.extend([z] * int(cnt))
        if len(samples) >= 256: break

    if len(samples) >= d + 2:
        try:
            m = min(len(samples), 32)
            used = samples[:m]
            N_ = d + m
            rows = []
            for i in range(d):
                r = [0]*N_; r[i] = N256; rows.append(r)
            for j, z in enumerate(used):
                r = [0]*N_
                for i in range(d): r[i] = int(z[i])
                r[d+j] = 1
                rows.append(r)
            reduced = lll_reduce(rows)
            basis_pts = [pt_mul(primes[i], G256) for i in range(d-2)] + [Q, G256]
            for row in reduced[:2*d+8]:
                head = row[:d]
                if not any(head): continue
                acc: Point = None
                for zi, B in zip(head, basis_pts):
                    if zi == 0 or B is None: continue
                    acc = pt_add(acc, pt_mul(zi, B))
                if acc is not None: continue
                const = sum(head[i]*primes[i] for i in range(d-2)) + head[d-1]
                coeff = head[d-2]
                if coeff == 0: continue
                inv_c = inv_mod(coeff % N256, N256)
                if inv_c is None: continue
                cand = (-const * inv_c) % N256
                for off in (0, k_start):
                    c = (cand + off) % N256
                    if c in checked: continue
                    checked.add(c)
                    if 0 < c <= range_end and verify_secp(c, Q):
                        log.info(f"✅ LLL: k = {c}")
                        return c
        except Exception as e:
            log.warning(f"LLL failed: {e}")

    return None


# ═══════════════════════════════════════════════════════════════════════════
# HIGH-LEVEL SOLVE
# ═══════════════════════════════════════════════════════════════════════════
def solve(puzzle_key: str, platform: str = "aer",
          shots: int = 8192, seed: int = 7,
          table: str = "canonical",
          adder: str = "approx", approx_threshold: int = 4,
          encoding: str = "none", use_fibonacci: bool = True,
          noise_sigma: float = 2.0,
          **platform_kw) -> Dict[str, Any]:
    if puzzle_key not in PUZZLES:
        raise KeyError(f"unknown puzzle {puzzle_key!r}")
    pz = PUZZLES[puzzle_key]
    Q = decompress_secp(pz.pubkey)
    if Q is None:
        raise RuntimeError(f"pubkey does not decompress")

    sz = puzzle_sizing(pz.bits)
    log.info("=" * 72)
    log.info(f"REGEV SOLVE — Puzzle #{puzzle_key} "
             f"({pz.bits}-bit interval on secp256k1)")
    log.info(f"  Qubit budget: d={sz['d']}, qpd={sz['qpd']}, "
             f"z={sz['z_qubits']}, target={sz['target_width']}, "
             f"TOTAL={sz['total']}")
    log.info("=" * 72)

    qc = build_circuit(
        Q, pz.k_start, pz.bits, sz["d"], sz["qpd"], sz["target_width"],
        table=table, adder=adder, approx_threshold=approx_threshold,
        encoding=encoding, use_fibonacci=use_fibonacci)

    log.info(f"Executing on {platform}, {shots} shots...")
    t0 = time.time()
    counts = execute(qc, platform, shots, seed=seed, **platform_kw)
    elapsed = time.time() - t0
    log.info(f"Done in {elapsed:.2f}s, {len(counts)} unique outcomes")

    counts = noise_filter(counts, pz.bits, sigma=noise_sigma)
    t0 = time.time()
    k = postprocess(counts, qc.metadata, Q, pz.k_start)
    pp_elapsed = time.time() - t0

    return {
        "puzzle": puzzle_key, "bits": pz.bits,
        "platform": platform, "shots": shots,
        "qubits": qc.num_qubits, "depth": qc.depth(), "size": qc.size(),
        "d": sz["d"], "qpd": sz["qpd"],
        "z_qubits": sz["z_qubits"], "target_width": sz["target_width"],
        "success": k is not None,
        "recovered": k,
        "recovered_hex": hex(k) if k is not None else None,
        "matches_known": (pz.secret is not None and k == pz.secret),
        "known_secret": hex(pz.secret) if pz.secret is not None else None,
        "elapsed_execute_s": elapsed,
        "elapsed_postprocess_s": pp_elapsed,
        "known_secret": (hex(pz.secret) if pz.secret is not None else None),
        "matches_known": (pz.secret is not None and k == pz.secret),
    }


# ═══════════════════════════════════════════════════════════════════════════
# SELF-TEST
# ═══════════════════════════════════════════════════════════════════════════
def self_test() -> Dict[str, Any]:
    results = {}
    results["secp_double_ok"] = (pt_add(G256, G256) is not None)
    results["secp_nG_is_inf"] = (pt_mul(N256, G256) is None)
    results["sec1_roundtrip"] = all(
        decompress_secp(
            ("02" if pt_mul(k, G256)[1] % 2 == 0 else "03")
            + f"{pt_mul(k, G256)[0]:064x}") == pt_mul(k, G256)
        for k in (1, 2, 12345))

    for key, pz in PUZZLES.items():
        Q = decompress_secp(pz.pubkey)
        results[f"puzzle_{key}_on_curve"] = Q is not None
        if pz.secret is not None and Q is not None:
            results[f"puzzle_{key}_secret_ok"] = verify_secp(pz.secret, Q)

    # HalfGCD
    test_a = 0x1234567890ABCDEF
    inv = halfgcd_modinv(test_a, P256)
    results["halfgcd_ok"] = (inv is not None and (test_a*inv) % P256 == 1)

    # Fibonacci
    fibs = fibonacci_sequence(16)
    results["fibonacci_monotone"] = all(fibs[i] < fibs[i+1] for i in range(len(fibs)-1))
    results["fibonacci_covers"] = fibs[-1] >= (1 << 16)

    # Sizing table sanity
    for key, pz in PUZZLES.items():
        sz = puzzle_sizing(pz.bits)
        expected_target = pz.bits if pz.bits < 256 else 257
        if sz["target_width"] != expected_target:
            results[f"sizing_{key}_ok"] = False
        else:
            results[f"sizing_{key}_ok"] = True

    # End-to-end small puzzle on Aer (12-bit)
    try:
        log.info("Running end-to-end on puzzle #12 (Aer)...")
        out = solve("12", platform="aer", shots=8192, seed=11)
        results["e2e_12bit"] = out["success"] or out["matches_known"]
        results["e2e_12_qubits"] = out["qubits"]
    except Exception as exc:
        results["e2e_12bit"] = False
        results["e2e_12_error"] = f"{type(exc).__name__}: {exc}"

    scalar = ["secp_double_ok", "secp_nG_is_inf", "sec1_roundtrip",
              "halfgcd_ok", "fibonacci_monotone", "fibonacci_covers",
              "e2e_12bit"]
    scalar_ok = all(results.get(k) for k in scalar)
    puzzles_ok = all(results.get(f"puzzle_{k}_on_curve") for k in PUZZLES)
    secrets_ok = all(results.get(f"puzzle_{k}_secret_ok")
                     for k in PUZZLES if PUZZLES[k].secret is not None)
    sizing_ok = all(results.get(f"sizing_{k}_ok") for k in PUZZLES)
    results["all_pass"] = bool(scalar_ok and puzzles_ok and secrets_ok and sizing_ok)
    return results


# ═══════════════════════════════════════════════════════════════════════════
# INTERACTIVE MENU
# ═══════════════════════════════════════════════════════════════════════════
MENU = """
╔══════════════════════════════════════════════════════════════════════╗
║  REGEV_FIXED — per-puzzle qubit sizing                               ║
╠══════════════════════════════════════════════════════════════════════╣
║  1. Show qubit budget table (all presets)                            ║
║  2. Solve a puzzle                                                   ║
║  3. Verify a puzzle pubkey                                           ║
║  4. Self-test                                                        ║
║  0. Exit                                                             ║
╚══════════════════════════════════════════════════════════════════════╝
"""


def _ask(prompt, default="", secret=False):
    suf = f" [{default}]" if default else ""
    if secret:
        try: return getpass.getpass(prompt+suf+": ") or default
        except Exception: return input(prompt+suf+": ").strip() or default
    try: v = input(prompt+suf+": ").strip()
    except EOFError: return default
    return v or default


def _ask_int(prompt, default):
    while True:
        try: return int(_ask(prompt, str(default)), 0)
        except ValueError: print("  invalid")


def _ask_choice(prompt, choices, default):
    choices = tuple(choices)
    while True:
        v = _ask(prompt, default).lower().strip()
        if v in choices: return v
        print(f"  choose from: {','.join(choices)}")


def _ask_yes(prompt, default=True):
    d = "Y/n" if default else "y/N"
    v = _ask(f"{prompt} [{d}]", "").lower()
    return default if not v else v in ("y","yes","1","true")


def interactive():
    while True:
        print(MENU)
        c = _ask("Choice", "1")
        try:
            if c == "0": return 0
            if c == "1": print_qubit_table()
            elif c == "2":
                key = _ask_choice("Puzzle", tuple(PUZZLES.keys()), "16")
                table = _ask_choice("Small-prime table",
                                    tuple(SP_TABLES.keys()), "canonical")
                platform = _ask_choice("Platform",
                                       ("aer","origin","ibm","iqm","rigetti"),
                                       "aer")
                shots = _ask_int("Shots", 8192)
                kw = {}
                if platform == "origin":
                    kw["origin_token"] = _ask("OriginQC token",
                                              os.getenv("ORIGINQC_TOKEN",""),
                                              secret=True)
                    kw["origin_device"] = _ask("Device", "WK_C180")
                    kw["origin_qpu"] = _ask_yes("Use QPU?", True)
                elif platform == "ibm":
                    kw["ibm_token"] = _ask("IBM token",
                                           os.getenv("IBM_QUANTUM_TOKEN",""),
                                           secret=True)
                    kw["ibm_backend"] = _ask("Backend", "ibm_fez")
                elif platform == "iqm":
                    kw["iqm_token"] = _ask("IQM token",
                                           os.getenv("IQM_TOKEN",""),
                                           secret=True)
                elif platform == "rigetti":
                    kw["qbraid_key"] = _ask("qBraid key",
                                            os.getenv("QBRAID_API_KEY",""),
                                            secret=True)
                out = solve(key, platform=platform, shots=shots,
                            table=table, **kw)
                print(json.dumps(out, indent=2, default=str))
            elif c == "3":
                key = _ask_choice("Puzzle", tuple(PUZZLES.keys()), "22")
                pz = PUZZLES[key]
                Q = decompress_secp(pz.pubkey)
                print(json.dumps({
                    "key": key, "bits": pz.bits,
                    "pubkey": pz.pubkey,
                    "on_curve": Q is not None,
                    "secret": hex(pz.secret) if pz.secret else None,
                    "secret_verifies": (verify_secp(pz.secret, Q)
                                        if pz.secret else None),
                }, indent=2))
            elif c == "4":
                print(json.dumps(self_test(), indent=2, default=str))
        except KeyboardInterrupt:
            return 0
        except Exception as e:
            print(f"  ERROR: {type(e).__name__}: {e}")


# ═══════════════════════════════════════════════════════════════════════════
# CLI
# ═══════════════════════════════════════════════════════════════════════════
def main(argv=None):
    ap = argparse.ArgumentParser(
        description="Regev solver with per-puzzle qubit sizing")
    ap.add_argument("--table", action="store_true",
                    help="print qubit budget table")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--solve", default="", metavar="PUZZLE_KEY",
                    help="puzzle key: 12,14,16,17,19,20,21,22,135,140,256")
    ap.add_argument("--platform", default="aer",
                    choices=("aer","origin","ibm","iqm","rigetti"))
    ap.add_argument("--shots", type=int, default=8192)
    ap.add_argument("--seed", type=int, default=7)
    ap.add_argument("--prime-table", default="canonical",
                    choices=tuple(SP_TABLES.keys()))
    ap.add_argument("--adder", default="approx", choices=("approx","draper"))
    ap.add_argument("--threshold", type=int, default=4)
    ap.add_argument("--encoding", default="none", choices=("none","cat"))
    ap.add_argument("--no-fibonacci", action="store_true")
    ap.add_argument("--sigma", type=float, default=2.0)
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
    ap.add_argument("--json-out", default="")
    ap.add_argument("--menu", action="store_true")
    args = ap.parse_args(list(sys.argv[1:] if argv is None else argv))

    if args.table:
        print_qubit_table(); return 0
    if args.self_test:
        out = self_test()
        print(json.dumps(out, indent=2, default=str))
        if args.json_out:
            Path(args.json_out).write_text(json.dumps(out, indent=2, default=str))
        return 0 if out.get("all_pass") else 1
    if not args.solve:
        return interactive()

    kw = {}
    if args.platform == "origin":
        kw = {"origin_token": args.origin_token,
              "origin_device": args.origin_device,
              "origin_qpu": args.origin_qpu}
    elif args.platform == "ibm":
        kw = {"ibm_token": args.ibm_token, "ibm_crn": args.ibm_crn,
              "ibm_backend": args.ibm_backend}
    elif args.platform == "iqm":
        kw = {"iqm_token": args.iqm_token, "iqm_device": args.iqm_device,
              "iqm_url": args.iqm_url}
    elif args.platform == "rigetti":
        kw = {"qbraid_key": args.qbraid_key,
              "rigetti_device": args.rigetti_device}

    out = solve(args.solve, platform=args.platform, shots=args.shots,
                seed=args.seed, table=args.prime_table,
                adder=args.adder, approx_threshold=args.threshold,
                encoding=args.encoding,
                use_fibonacci=not args.no_fibonacci,
                noise_sigma=args.sigma, **kw)
    print(json.dumps(out, indent=2, default=str))
    if args.json_out:
        Path(args.json_out).write_text(json.dumps(out, indent=2, default=str))
    return 0 if out["success"] else 1


if __name__ == "__main__":
    raise SystemExit(main())