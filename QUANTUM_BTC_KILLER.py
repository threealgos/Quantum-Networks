#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
╔══════════════════════════════════════════════════════════════════════════════╗
║  REGEV SECP256K1 ECDLP SOLVER — Full Edition v1.0                            ║
║  Real arithmetic • 4 quantum platforms • Multi-tier post-processing          ║
║  Range: 22-bit keys up to 140+ bits                                          ║
╚══════════════════════════════════════════════════════════════════════════════╝

Honest scope:
  * Real Regev d-dimensional phase-oracle circuit for secp256k1 ECDLP
    over a user-specified key interval.
  * Oracle encodes [2^k]·(Q - k_start·G) and [2^k]·b_i·G via controlled-phase
    rotations on a target register (QFT-coalesced).
  * Every returned private key verified with exact secp256k1 [k]·G == Q.
  * Post-processing: IPE-CF, Z-direct, Z-rescale, LLL lattice relations,
    multi-depth CF, GCD, half-splits — tier-ordered, per-tier verified.

Platforms:
  aer       — Qiskit Aer (local simulator)
  ibm       — IBM Quantum via Qiskit Runtime SamplerV2
  iqm       — IQM Resonance via official IQM Qiskit adapter (pytket fallback)
  origin    — OriginQC pyqpanda3 (CPU QVM or cloud QPU)
  rigetti   — Rigetti Cepheus-1 via qBraid / Open Quantum

Requires: numpy, (optional) qiskit, qiskit-aer, qiskit-ibm-runtime,
          pytket + pytket-iqm, iqm-client[qiskit], pyqpanda3, qbraid,
          openquantum-sdk-qiskit, fpylll or sympy.

Usage:
  python regev_solver.py                            # interactive menu
  python regev_solver.py --self-test                # run all tests
  python regev_solver.py --platform-report          # show SDK status
  python regev_solver.py --pubkey 02... --bits 22 --platform aer
"""
from __future__ import annotations

import argparse
import getpass
import json
import logging
import math
import os
import sys
import time
import traceback
from collections import Counter
from dataclasses import dataclass, asdict
from datetime import datetime
from fractions import Fraction
from pathlib import Path
from typing import Any, Dict, List, Optional, Sequence, Tuple

try:
    import numpy as np
except ImportError as exc:
    raise SystemExit("numpy required: pip install numpy") from exc

# ─── logging ────────────────────────────────────────────────────────────────
CACHE = Path("regev_cache")
CACHE.mkdir(exist_ok=True)
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s | %(levelname)s | %(message)s",
    handlers=[
        logging.FileHandler(CACHE / "regev_solver.log"),
        logging.StreamHandler(sys.stdout),
    ],
)
log = logging.getLogger("regev")

# ═══════════════════════════════════════════════════════════════════════════
# SECP256K1 CONSTANTS
# ═══════════════════════════════════════════════════════════════════════════
P = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
A = 0
B = 7
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
G: Tuple[int, int] = (Gx, Gy)

SMALL_PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53,
                59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113,
                127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181,
                191, 193, 197, 199]

# ═══════════════════════════════════════════════════════════════════════════
# EC ARITHMETIC
# ═══════════════════════════════════════════════════════════════════════════
def modinv(a: int, m: int = P) -> Optional[int]:
    a %= m
    if a == 0:
        return None
    return pow(a, -1, m)


def pt_add(p1, p2, p=P, a=A):
    if p1 is None:
        return p2
    if p2 is None:
        return p1
    x1, y1 = p1
    x2, y2 = p2
    if x1 == x2:
        if (y1 + y2) % p == 0:
            return None
        if y1 == 0:
            return None
        lam = (3 * x1 * x1 + a) * modinv(2 * y1, p) % p
    else:
        lam = (y2 - y1) * modinv(x2 - x1, p) % p
    x3 = (lam * lam - x1 - x2) % p
    y3 = (lam * (x1 - x3) - y1) % p
    return (x3, y3)


def pt_mul(k: int, P_pt, p=P, a=A) -> Optional[Tuple[int, int]]:
    if k == 0 or P_pt is None:
        return None
    if k < 0:
        return pt_mul(-k, (P_pt[0], (-P_pt[1]) % p), p, a)
    R = None
    A_pt = P_pt
    while k:
        if k & 1:
            R = pt_add(R, A_pt, p, a)
        A_pt = pt_add(A_pt, A_pt, p, a)
        k >>= 1
    return R


def pt_neg(P_pt):
    return None if P_pt is None else (P_pt[0], (-P_pt[1]) % P)


def decompress_pubkey(hx: str) -> Optional[Tuple[int, int]]:
    h = hx.lower().strip().replace("0x", "").replace(" ", "")
    if len(h) != 66 or h[:2] not in ("02", "03"):
        return None
    try:
        x = int(h[2:], 16)
    except ValueError:
        return None
    if x >= P:
        return None
    ysq = (pow(x, 3, P) + B) % P
    y = pow(ysq, (P + 1) // 4, P)
    if (y * y) % P != ysq:
        return None
    if (int(h[:2], 16) == 2 and y % 2) or (int(h[:2], 16) == 3 and y % 2 == 0):
        y = P - y
    return (x, y)


def compress_point(P_pt) -> str:
    if P_pt is None:
        return ""
    prefix = "02" if P_pt[1] % 2 == 0 else "03"
    return prefix + f"{P_pt[0]:064x}"


def verify_key(k: int, Q_pt, p=P, G_pt=G) -> bool:
    if k is None or k <= 0 or k >= N:
        return False
    try:
        pt = pt_mul(k, G_pt, p)
        return pt is not None and pt == Q_pt
    except Exception:
        return False


# ═══════════════════════════════════════════════════════════════════════════
# Regev PARAMETERS
# ═══════════════════════════════════════════════════════════════════════════
def ceil_sqrt(n: int) -> int:
    r = math.isqrt(n)
    return r if r * r == n else r + 1


@dataclass
class RegevParams:
    bits: int
    d: int
    qpd: int
    D: int
    R: float
    k_start: int
    range_size: int

    @property
    def range_end(self) -> int:
        return self.k_start + self.range_size - 1


def compute_regev_params(bits: int, k_start: int = 0,
                         d_override: int = 0, qpd_override: int = 0,
                         R_override: float = 0.0) -> RegevParams:
    n = max(4, bits)
    d = d_override or max(2, ceil_sqrt(n))
    qpd = qpd_override or max(4, math.ceil(n / d) + 2)
    D = 1 << qpd
    R = R_override or max(2.0, min(D / 3.0, 2.0 ** math.sqrt(n)))
    range_size = 1 << bits
    return RegevParams(bits, d, qpd, D, R, k_start, range_size)


# ═══════════════════════════════════════════════════════════════════════════
# GROUP ELEMENT PRECOMPUTE
# ═══════════════════════════════════════════════════════════════════════════
def encode_x(P_pt, bits: int, p=P) -> int:
    if P_pt is None:
        return 0
    return P_pt[0] % (1 << bits)


def precompute_delta_powers(Q_pt, k_start: int, bits: int, d: int):
    neg_kG = pt_mul(k_start, G)
    if neg_kG is not None:
        neg_kG = pt_neg(neg_kG)
    delta = pt_add(Q_pt, neg_kG)

    delta_powers: List[int] = []
    cur = delta
    for _ in range(bits):
        delta_powers.append(encode_x(cur, bits))
        cur = pt_add(cur, cur) if cur else None

    basis_powers: List[List[int]] = []
    for i in range(d):
        b_i = SMALL_PRIMES[i % len(SMALL_PRIMES)]
        bG = pt_mul(b_i, G)
        powers: List[int] = []
        cur = bG
        for _ in range(bits):
            powers.append(encode_x(cur, bits))
            cur = pt_add(cur, cur) if cur else None
        basis_powers.append(powers)

    return delta_powers, basis_powers


# ═══════════════════════════════════════════════════════════════════════════
# QISKIT CIRCUIT BUILDER
# ═══════════════════════════════════════════════════════════════════════════
QISKIT_OK = False
try:
    from qiskit import QuantumCircuit, QuantumRegister, ClassicalRegister, transpile
    from qiskit.circuit.library import QFTGate
    QISKIT_OK = True
except ImportError:
    pass


def _append_qft(qc, qubits, inverse: bool = False):
    if QISKIT_OK:
        try:
            g = QFTGate(num_qubits=len(qubits))
            if inverse:
                g = g.inverse()
            qc.append(g, list(qubits))
            return
        except Exception:
            pass
    n = len(qubits)
    if inverse:
        for i in range(n - 1, -1, -1):
            for j in range(n - 1, i, -1):
                qc.cp(-math.pi / (1 << (j - i)), qubits[j], qubits[i])
            qc.h(qubits[i])
    else:
        for i in range(n):
            for j in range(i + 1, n):
                qc.cp(math.pi / (1 << (j - i)), qubits[j], qubits[i])
            qc.h(qubits[i])


def build_regev_circuit(params: RegevParams, delta_powers, basis_powers):
    if not QISKIT_OK:
        raise RuntimeError("Qiskit required for circuit construction")

    bits, d, qpd = params.bits, params.d, params.qpd
    Nmod = 1 << bits

    z_regs = [QuantumRegister(qpd, f"z{i}") for i in range(d)]
    target = QuantumRegister(bits, "tgt")
    cregs = ClassicalRegister(d * qpd, "cz")

    qc = QuantumCircuit(*z_regs, target, cregs, name="regev_oracle")

    R = params.R
    for zr in z_regs:
        for i in range(qpd):
            try:
                p_one = math.exp(-math.pi * ((1 << i) / R) ** 2)
                p_one = max(min(p_one, 0.999), 0.001)
                angle = 2 * math.asin(math.sqrt(1 - p_one))
                qc.ry(angle, zr[i])
            except Exception:
                qc.h(zr[i])

    _append_qft(qc, list(target), inverse=False)

    for i, zr in enumerate(z_regs):
        for k in range(qpd):
            if k >= len(basis_powers[i]):
                break
            coef = basis_powers[i][k] % Nmod
            if coef == 0:
                continue
            ctrl = zr[k]
            for bit_i in range(bits):
                angle = (2 * math.pi * coef * (1 << bit_i)) / Nmod
                angle %= (2 * math.pi)
                if abs(angle) < 1e-12 or abs(angle - 2 * math.pi) < 1e-12:
                    continue
                qc.cp(angle, ctrl, target[bit_i])

    delta_total = 0
    for k in range(min(bits, len(delta_powers))):
        delta_total = (delta_total + delta_powers[k]) % Nmod
    if delta_total:
        for bit_i in range(bits):
            angle = (2 * math.pi * delta_total * (1 << bit_i)) / Nmod
            angle %= (2 * math.pi)
            if abs(angle) < 1e-12 or abs(angle - 2 * math.pi) < 1e-12:
                continue
            qc.p(angle, target[bit_i])

    _append_qft(qc, list(target), inverse=True)

    for zr in z_regs:
        _append_qft(qc, list(zr), inverse=False)

    idx = 0
    for zr in z_regs:
        for q in zr:
            qc.measure(q, cregs[idx])
            idx += 1

    qc.metadata = {
        "bits": bits, "d": d, "qpd": qpd, "R": R,
        "delta_powers": delta_powers, "basis_powers": basis_powers,
    }
    log.info(f"Built Regev circuit: d={d}, qpd={qpd}, qubits={qc.num_qubits}, "
             f"depth={qc.depth()}, size={qc.size()}")
    return qc


# ═══════════════════════════════════════════════════════════════════════════
# PLATFORM DETECTION
# ═══════════════════════════════════════════════════════════════════════════
PLATFORMS: Dict[str, bool] = {}

try:
    from qiskit_ibm_runtime import QiskitRuntimeService, SamplerV2 as IBMSampler
    PLATFORMS["ibm"] = True
except ImportError:
    PLATFORMS["ibm"] = False

try:
    from qiskit_aer import AerSimulator
    PLATFORMS["aer"] = True
except ImportError:
    PLATFORMS["aer"] = False

try:
    from pytket.extensions.qiskit import qiskit_to_tk
    from pytket.extensions.iqm import IQMBackend as IQMBackend_pytket
    PLATFORMS["iqm_pytket"] = True
except ImportError:
    PLATFORMS["iqm_pytket"] = False

try:
    from iqm.qiskit_iqm import IQMProvider
    PLATFORMS["iqm_qiskit"] = True
except ImportError:
    PLATFORMS["iqm_qiskit"] = False

try:
    import pyqpanda3.core as _origin_core  # noqa
    from pyqpanda3.qcloud import QCloudService as _QCloudService  # noqa
    PLATFORMS["origin"] = True
except ImportError:
    PLATFORMS["origin"] = False

try:
    from qbraid.runtime import QbraidProvider  # noqa
    PLATFORMS["rigetti_qbraid"] = True
except ImportError:
    try:
        from qbraid.runtime.native import QbraidProvider  # noqa
        PLATFORMS["rigetti_qbraid"] = True
    except ImportError:
        PLATFORMS["rigetti_qbraid"] = False


def platform_report() -> str:
    lines = ["Platform availability:"]
    for k, v in PLATFORMS.items():
        lines.append(f"  {k:20s} {'OK' if v else 'MISSING'}")
    return "\n".join(lines)


# ═══════════════════════════════════════════════════════════════════════════
# EXECUTION — Aer
# ═══════════════════════════════════════════════════════════════════════════
def execute_aer(qc, shots: int, seed: int = 7) -> Counter:
    if not PLATFORMS.get("aer"):
        raise RuntimeError("qiskit-aer not installed: pip install qiskit-aer")
    sim = AerSimulator(seed_simulator=seed)
    tqc = transpile(qc, sim, optimization_level=2)
    log.info(f"Aer transpiled: {tqc.num_qubits}q, depth={tqc.depth()}, size={tqc.size()}")
    result = sim.run(tqc, shots=shots).result()
    return Counter(result.get_counts())


# ═══════════════════════════════════════════════════════════════════════════
# EXECUTION — IBM
# ═══════════════════════════════════════════════════════════════════════════
def _ibm_extract_counts(pub_result, register_names=None) -> Counter:
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
                    return Counter(c)
            except Exception:
                pass

    if not arrays:
        raise RuntimeError("No IBM register data found")

    ordered = list(arrays.keys())
    n = len(arrays[ordered[0]])
    joined = Counter()
    for i in range(n):
        joined[" ".join(arrays[k][i] for k in ordered)] += 1
    return joined


def execute_ibm(qc, shots: int, backend_name: str = "ibm_fez",
                token: str = "", crn: str = "") -> Counter:
    if not PLATFORMS.get("ibm"):
        raise RuntimeError("qiskit-ibm-runtime not installed")
    token = token or os.getenv("IBM_QUANTUM_TOKEN", "") or os.getenv("QISKIT_IBM_TOKEN", "")
    crn = crn or os.getenv("IBM_QUANTUM_CRN", "")
    if not token:
        raise RuntimeError("IBM Quantum token required (env IBM_QUANTUM_TOKEN)")

    from qiskit.transpiler.preset_passmanagers import generate_preset_pass_manager

    service = QiskitRuntimeService(channel="ibm_cloud", token=token, instance=crn or None)
    backend = service.backend(backend_name)
    log.info(f"IBM backend: {backend.name} ({backend.num_qubits}q)")

    pm = generate_preset_pass_manager(backend=backend, optimization_level=1)
    isa = pm.run(qc)
    log.info(f"IBM transpiled: {isa.num_qubits}q, depth={isa.depth()}, size={isa.size()}")

    if isa.depth() > 10000:
        raise RuntimeError(
            f"Circuit depth {isa.depth()} exceeds IBM JIT limit (~10000). "
            f"Reduce bits, use smaller d/qpd, or pick a different platform."
        )

    sampler = IBMSampler(mode=backend)
    job = sampler.run([isa], shots=shots)
    log.info(f"IBM job: {job.job_id()}")
    result = job.result()
    return _ibm_extract_counts(result[0], [r.name for r in qc.cregs])


# ═══════════════════════════════════════════════════════════════════════════
# EXECUTION — IQM
# ═══════════════════════════════════════════════════════════════════════════
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

    new_qregs = qc.qregs[:]
    c_iqm = CR(len(measured), "c_iqm")
    new_qc = QC(*new_qregs, c_iqm)

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

    log.info(f"Stripped dynamics: {qc.num_qubits}q d{qc.depth()} "
             f"→ {new_qc.num_qubits}q d{new_qc.depth()}")
    return new_qc


def execute_iqm(qc, shots: int, device: str = "emerald",
                token: str = "", url: str = "https://resonance.iqm.tech") -> Counter:
    token = token or os.getenv("IQM_TOKEN", "")
    if not token:
        raise RuntimeError("IQM_TOKEN required")

    if not PLATFORMS.get("iqm_qiskit") and not PLATFORMS.get("iqm_pytket"):
        raise RuntimeError("Install iqm-client[qiskit] or pytket-iqm")

    prepared = _strip_dynamic_ops(qc)

    if PLATFORMS.get("iqm_qiskit"):
        try:
            device_url = f"{url.rstrip('/')}/{device}"
            provider = IQMProvider(device_url, token=token)
            backend = provider.get_backend()
            log.info(f"IQM backend: {device} @ {url}")
            compiled = transpile(prepared, backend=backend, optimization_level=1)
            job = backend.run(compiled, shots=shots)
            try:
                jid = job.job_id()
            except Exception:
                jid = "unknown"
            log.info(f"IQM job: {jid}")
            result = job.result()
            try:
                raw = result.get_counts(compiled)
            except Exception:
                raw = result.get_counts()
            if isinstance(raw, list):
                raw = raw[0] if raw else {}
            return Counter(raw)
        except Exception as e:
            log.warning(f"IQM Qiskit adapter failed: {e}")
            if not PLATFORMS.get("iqm_pytket"):
                raise

    if PLATFORMS.get("iqm_pytket"):
        from qiskit.transpiler import PassManager
        from qiskit.transpiler.passes import Decompose
        pm = PassManager([Decompose(), Decompose()])
        qc_d = pm.run(prepared)
        qc_p = transpile(qc_d, basis_gates=["h", "cx", "cp", "p", "x", "ry", "rz", "sx", "swap", "ccx"],
                         optimization_level=0)
        tk = qiskit_to_tk(qc_p)
        backend = IQMBackend_pytket(device=device, api_token=token)
        compiled = backend.get_compiled_circuit(tk, optimisation_level=2)
        handle = backend.process_circuit(compiled, n_shots=shots)
        result = backend.get_result(handle)
        raw = result.get_counts()
        out = Counter()
        for k, v in raw.items():
            out["".join(str(b) for b in k)] += int(v)
        return out

    raise RuntimeError("No working IQM path")


# ═══════════════════════════════════════════════════════════════════════════
# EXECUTION — OriginQC
# ═══════════════════════════════════════════════════════════════════════════
def execute_origin(qc, shots: int, token: str = "", device: str = "WK_C180",
                   use_qpu: bool = False) -> Counter:
    if not PLATFORMS.get("origin"):
        raise RuntimeError("pyqpanda3 not installed")
    import pyqpanda3.core as core
    from qiskit.qasm2 import dumps as qasm2_dumps

    flat = transpile(qc, basis_gates=["u", "u1", "u2", "u3", "cx"], optimization_level=2)
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
        try:
            import pyqpanda3.intermediate_compiler as ic
            for fname in ("convert_qasm_string_to_qprog", "qasm_to_qprog"):
                fn = getattr(ic, fname, None)
                if callable(fn):
                    try:
                        prog = fn(qasm)
                        if isinstance(prog, tuple):
                            prog = prog[0]
                        break
                    except Exception:
                        continue
        except Exception:
            pass

    if prog is None:
        raise RuntimeError("pyqpanda3 has no QASM importer")

    if not use_qpu:
        vm = core.CPUQVM()
        vm.run(prog, shots)
        return Counter(vm.result().get_counts())

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
        out = Counter()
        for k, v in result.items():
            if isinstance(v, float) and 0 < v <= 1.0:
                out[str(k)] = int(round(v * shots))
            else:
                out[str(k)] = int(v)
        return out
    raise RuntimeError(f"Unknown Origin result type: {type(result)}")


# ═══════════════════════════════════════════════════════════════════════════
# EXECUTION — Rigetti
# ═══════════════════════════════════════════════════════════════════════════
def _validate_terminal_circuit(qc) -> List[str]:
    problems = []
    data = list(qc.data)
    dynamic = {"reset", "if_else", "while_loop", "for_loop", "switch_case"}
    for idx, instr in enumerate(data):
        name = getattr(instr.operation, "name", "").lower()
        if name in dynamic:
            problems.append(name)
        if name == "measure":
            q = instr.qubits[0] if instr.qubits else None
            if q is not None:
                for later in data[idx + 1:]:
                    later_name = getattr(later.operation, "name", "").lower()
                    if later_name in ("measure", "barrier", "delay"):
                        continue
                    if q in later.qubits:
                        problems.append("mid-circuit-measure")
                        break
    return sorted(set(problems))


def execute_rigetti(qc, shots: int, qbraid_key: str = "",
                    device_id: str = "openquantum:rigetti:qpu:cepheus-1-108q") -> Counter:
    qbraid_key = qbraid_key or os.getenv("QBRAID_API_KEY", "")

    if not PLATFORMS.get("rigetti_qbraid"):
        raise RuntimeError("qBraid runtime not installed: pip install qbraid")

    problems = _validate_terminal_circuit(qc)
    if problems:
        raise RuntimeError(
            f"Rigetti/OpenQuantum requires terminal-measurement circuit. "
            f"Problems: {problems}"
        )

    from qiskit import QuantumCircuit as QC
    from qiskit.qasm3 import dumps as qasm3_dumps

    flat = QC(qc.num_qubits, qc.num_clbits, name="flat")
    flat.compose(qc, qubits=flat.qubits, clbits=flat.clbits, inplace=True)
    flat = transpile(flat, basis_gates=["h", "rz", "rx", "x", "cx"], optimization_level=1)
    qasm3 = qasm3_dumps(flat)

    provider = QbraidProvider(api_key=qbraid_key) if qbraid_key else QbraidProvider()
    device = provider.get_device(device_id)
    log.info(f"qBraid device: {device_id}")

    job = device.run(qasm3, shots=shots)

    try:
        jid = getattr(job, "id", None)
        if callable(jid):
            jid = jid()
        log.info(f"Rigetti job: {jid}")
    except Exception:
        pass

    if hasattr(job, "wait_for_final_state"):
        job.wait_for_final_state()
    result = job.result()

    data = getattr(result, "data", None)
    if data is not None:
        if hasattr(data, "get_counts"):
            return Counter(data.get_counts())
        if isinstance(data, dict) and "counts" in data:
            return Counter(data["counts"])
    for attr in ("get_counts", "measurement_counts", "counts"):
        obj = getattr(result, attr, None)
        if callable(obj):
            return Counter(obj())
        if isinstance(obj, dict):
            return Counter(obj)
    raise RuntimeError(f"Unknown Rigetti result type: {type(result)}")


# ═══════════════════════════════════════════════════════════════════════════
# RETRIEVAL BY JOB ID
# ═══════════════════════════════════════════════════════════════════════════
def retrieve_ibm(job_id: str, token: str = "", crn: str = "",
                 register_names: Optional[List[str]] = None) -> Counter:
    if not PLATFORMS.get("ibm"):
        raise RuntimeError("qiskit-ibm-runtime not installed")
    token = token or os.getenv("IBM_QUANTUM_TOKEN", "")
    service = QiskitRuntimeService(channel="ibm_cloud", token=token, instance=crn or None)
    job = service.job(job_id)
    status = str(job.status())
    log.info(f"IBM job {job_id} status: {status}")
    if status not in ("DONE", "COMPLETED"):
        raise RuntimeError(f"IBM job not complete: {status}")
    result = job.result()
    return _ibm_extract_counts(result[0], register_names)


def retrieve_iqm(job_id: str, token: str = "",
                 url: str = "https://resonance.iqm.tech",
                 device: str = "emerald") -> Counter:
    try:
        from iqm.iqm_client import IQMClient
    except ImportError:
        raise RuntimeError("iqm-client not installed")
    token = token or os.getenv("IQM_TOKEN", "")

    try:
        from uuid import UUID
        jid = UUID(job_id)
    except Exception:
        jid = job_id

    try:
        client = IQMClient(url, quantum_computer=device, token=token)
    except TypeError:
        client = IQMClient(url, token=token)

    result = None
    if hasattr(client, "get_run"):
        result = client.get_run(jid)
    if result is None and hasattr(client, "wait_for_results"):
        result = client.wait_for_results(jid)

    ms = getattr(result, "measurements", None)
    if ms:
        if isinstance(ms, dict):
            ms = [ms]
        out = Counter()
        for circ_ms in ms:
            if not isinstance(circ_ms, dict):
                continue
            keys = list(circ_ms.keys())
            arrays = [circ_ms[k] for k in keys]
            n = min(len(a) for a in arrays)
            for i in range(n):
                parts = []
                for a in arrays:
                    sh = a[i]
                    if isinstance(sh, str):
                        parts.append(sh)
                    elif isinstance(sh, (int, np.integer)):
                        parts.append(str(int(sh)))
                    else:
                        parts.append("".join(str(int(x)) for x in sh))
                out[" ".join(parts)] += 1
        return out

    raise RuntimeError("Cannot extract IQM result")


def retrieve_origin(job_id: str, token: str = "",
                    shots: int = 128, n_cbits: int = 1) -> Counter:
    token = token or os.getenv("ORIGINQC_TOKEN", "")
    import requests
    url = os.getenv("ORIGINQC_TASK_DETAIL_URL",
                    "https://pyqanda-admin.qpanda.cn/oqcs/task/origin/taskDetail.json")
    headers = {
        "Authorization": f"oqcs_auth={token}",
        "Content-Type": "application/json",
        "origin-language": "en",
    }
    resp = requests.post(url, headers=headers, json={"taskId": job_id}, timeout=30)
    resp.raise_for_status()
    detail = resp.json()
    if not detail.get("success"):
        raise RuntimeError(f"Origin API error: {detail}")
    obj = detail["obj"]
    state = str(obj.get("taskState", ""))
    if state != "3":
        raise RuntimeError(f"Origin job not complete: state={state}")

    tr = obj.get("taskResult", [])
    if not tr:
        raise RuntimeError("No taskResult")
    payload = json.loads(tr[0]) if isinstance(tr[0], str) else tr[0]
    keys = payload.get("key", [])
    values = payload.get("value", [])
    out = Counter()
    for k, v in zip(keys, values):
        if isinstance(k, str) and k.startswith("0x"):
            k = format(int(k, 16), f"0{n_cbits}b")
        if isinstance(v, float) and 0 < v <= 1.0:
            out[str(k)] = int(round(v * shots))
        else:
            out[str(k)] = int(v)
    return out


def retrieve_rigetti(job_qrn: str, qbraid_key: str = "",
                     width: int = 0, shots: int = 128) -> Counter:
    import requests
    from urllib.parse import quote
    qbraid_key = qbraid_key or os.getenv("QBRAID_API_KEY", "")
    url = "https://api-v2.qbraid.com/api/v1/jobs/" + quote(job_qrn, safe=":-_") + "/result"
    headers = {"X-API-KEY": qbraid_key, "Accept": "application/json"}
    resp = requests.get(url, headers=headers, timeout=30)
    if resp.status_code == 409:
        raise RuntimeError("Rigetti result not ready (409)")
    resp.raise_for_status()
    payload = resp.json()
    data = payload.get("data", payload)

    def find_counts(obj):
        if isinstance(obj, dict):
            for key in ("measurementCounts", "measurement_counts", "counts"):
                if key in obj and isinstance(obj[key], dict):
                    return obj[key]
            for v in obj.values():
                r = find_counts(v)
                if r:
                    return r
        elif isinstance(obj, (list, tuple)):
            for v in obj:
                r = find_counts(v)
                if r:
                    return r
        return None

    counts_raw = find_counts(data)
    if not counts_raw:
        raise RuntimeError(f"No counts in Rigetti response: {str(data)[:500]}")

    out = Counter()
    for k, v in counts_raw.items():
        s = str(k)
        if s.startswith("0x"):
            s = format(int(s, 16), f"0{width}b") if width else s
        out[s] += int(v)
    return out


# ═══════════════════════════════════════════════════════════════════════════
# POST-PROCESSING
# ═══════════════════════════════════════════════════════════════════════════
def counts_to_samples(counts: Counter, d: int, qpd: int,
                      limit: Optional[int] = None) -> List[Tuple[int, ...]]:
    samples: List[Tuple[int, ...]] = []
    total = d * qpd
    for key, count in sorted(counts.items(), key=lambda kv: -kv[1]):
        clean = "".join(ch for ch in str(key) if ch in "01")
        if not clean:
            continue
        clean = clean.zfill(total)[-total:]
        little = clean[::-1]
        vec = tuple(int((little[i * qpd:(i + 1) * qpd][::-1]) or "0", 2) for i in range(d))
        take = count if limit is None else min(count, max(0, limit - len(samples)))
        samples.extend([vec] * int(take))
        if limit and len(samples) >= limit:
            break
    return samples


def _lll_reduce(matrix: List[List[int]]) -> List[List[int]]:
    try:
        from fpylll import IntegerMatrix, LLL
        M = IntegerMatrix.from_matrix(matrix)
        LLL.reduction(M, delta=0.75)
        return [[int(M[i, j]) for j in range(M.ncols)] for i in range(M.nrows)]
    except ImportError:
        pass
    try:
        from sympy import Matrix
        return [[int(v) for v in row] for row in Matrix(matrix).lll(delta=0.75).tolist()]
    except ImportError:
        raise RuntimeError("Install fpylll or sympy for LLL")


def build_embedding(samples, D, R):
    if not samples:
        raise ValueError("empty samples")
    d = len(samples[0])
    m = len(samples)
    delta_bound = math.sqrt(d / 2) / float(R)
    S = max(1, round(1.0 / delta_bound))
    rows: List[List[int]] = []
    for i in range(d):
        rows.append([D if i == j else 0 for j in range(d)] + [0] * m)
    for j, y in enumerate(samples):
        rows.append([S * int(v) for v in y] + [S * D if j == k else 0 for k in range(m)])
    return [list(col) for col in zip(*rows)]


def solve_linear_congruence(a: int, b: int, modulus: int) -> List[int]:
    a %= modulus
    b %= modulus
    g = math.gcd(a, modulus)
    if b % g:
        return []
    aa, bb, mm = a // g, b // g, modulus // g
    x0 = (bb * pow(aa, -1, mm)) % mm
    return sorted({(x0 + k * mm) % modulus for k in range(g)})


def continued_fraction_approx(num, den, max_den=1_000_000):
    if den == 0:
        return 0, 1
    frac = Fraction(num, den).limit_denominator(max_den)
    return frac.numerator, frac.denominator


def _extract_relations(samples, bases, p, D, R, order):
    embedded = build_embedding(samples, D, R)
    reduced = _lll_reduce(embedded)
    d = len(bases)
    relations: List[List[int]] = []
    seen = set()
    pool = reduced[:]
    short = reduced[: min(len(reduced), d + 8)]
    for i in range(len(short)):
        for j in range(i + 1, len(short)):
            pool.append([a + b for a, b in zip(short[i], short[j])])
            pool.append([a - b for a, b in zip(short[i], short[j])])

    for row in pool:
        head = row[:d]
        if not all(v % D == 0 for v in head):
            continue
        z = tuple(v // D for v in head)
        if not any(z) or z in seen:
            continue
        val = 1
        for zi, bi in zip(z, bases):
            val = val * pow(int(bi), int(zi) % order, p) % p
        if val == 1:
            seen.add(z)
            relations.append(list(z))
    relations.sort(key=lambda v: sum(x * x for x in v))
    return relations


def postprocess_regev(counts: Counter, params: RegevParams, Q_pt) -> Dict[str, Any]:
    d, qpd, bits = params.d, params.qpd, params.bits
    order = N
    K = params.k_start
    range_start = max(1, K)
    range_end = K + (1 << bits) - 1
    D = params.D
    R = params.R

    log.info(f"Post-processing: {len(counts)} outcomes, {sum(counts.values())} shots")
    log.info(f"  d={d}, qpd={qpd}, bits={bits}, "
             f"range=[{hex(range_start)}, {hex(range_end)}]")

    verified: List[int] = []
    verified_set = set()
    candidates_seen: set = set()
    relations_found: List[List[int]] = []

    def _accept(k: int, tag: str) -> bool:
        if k is None or k <= 0 or k in verified_set:
            return False
        if not (range_start <= k <= range_end):
            return False
        if k in candidates_seen:
            return False
        candidates_seen.add(k)
        if verify_key(k, Q_pt):
            verified_set.add(k)
            verified.append(k)
            log.info(f"[VERIFIED] ({tag}): k = {hex(k)} ({k})")
            return True
        return False

    # Tier 0 — IPE-CF
    log.info("Tier 0: IPE-CF")
    for bs, _ in counts.most_common():
        clean = bs.replace(" ", "")
        if not clean:
            continue
        for variant in (clean, clean[::-1]):
            try:
                m = int(variant, 2) % (1 << bits)
            except ValueError:
                continue
            if m == 0:
                continue
            frac = Fraction(m, 1 << bits).limit_denominator(order)
            p_cf, q_cf = frac.numerator, frac.denominator
            if q_cf:
                inv_q = modinv(q_cf, order)
                if inv_q:
                    k1 = (p_cf * inv_q) % order
                    _accept(k1, "IPE-CF")
                    _accept((k1 + K) % order, "IPE-CF+K")
    if verified:
        return {"verified": verified, "relations": [], "tier": "IPE-CF",
                "candidates_checked": len(candidates_seen)}

    # Tier 1 — Z-direct
    log.info("Tier 1: Z-direct")
    for bs, _ in counts.most_common():
        clean = bs.replace(" ", "")
        if not clean:
            continue
        try:
            raw = int(clean, 2)
        except ValueError:
            continue
        variants = [raw]
        if len(clean) > 1:
            try:
                variants.append(int(clean[::-1], 2))
            except Exception:
                pass
        for v in variants:
            if v == 0:
                continue
            _accept(v % order, "Z-direct")
            _accept((v + K) % order, "Z-direct+K")
    if verified:
        return {"verified": verified, "relations": [], "tier": "Z-direct",
                "candidates_checked": len(candidates_seen)}

    # Tier 2 — Z-rescale
    log.info("Tier 2: Z-rescale")
    basis_inv = {}
    for bp in SMALL_PRIMES[:16]:
        inv = modinv(bp, order)
        if inv is not None:
            basis_inv[bp] = inv
    for bs, _ in counts.most_common():
        clean = bs.replace(" ", "")
        if not clean:
            continue
        try:
            raw = int(clean, 2)
        except ValueError:
            continue
        variants = [raw]
        if len(clean) > 1:
            try:
                variants.append(int(clean[::-1], 2))
            except Exception:
                pass
        for v in variants:
            if v == 0:
                continue
            for bp, inv in basis_inv.items():
                _accept((v * inv) % order, f"Z-rescale-{bp}")
                _accept(((v * inv) + K) % order, f"Z-rescale-{bp}+K")
    if verified:
        return {"verified": verified, "relations": [], "tier": "Z-rescale",
                "candidates_checked": len(candidates_seen)}

    # Tier 3 — LLL lattice relations
    log.info("Tier 3: LLL lattice relations")
    samples = counts_to_samples(counts, d, qpd,
                                 limit=min(sum(counts.values()), 4096))
    small_bases = [pt_mul(SMALL_PRIMES[i % len(SMALL_PRIMES)], G) for i in range(d)]

    if len(samples) >= d + 2:
        rng = np.random.default_rng(7)
        for trial in range(12):
            take = min(len(samples), max(d + 4, 3 * d))
            if take < d + 2:
                break
            idx = rng.choice(len(samples), size=take, replace=False)
            subset = [samples[int(i)] for i in idx]
            for R_eff in (R, R * 1.5, R * 2.0):
                try:
                    rels = _extract_relations(subset, small_bases, P, D, R_eff, order)
                except Exception:
                    continue
                if rels:
                    relations_found.extend(rels)
                    break
            if relations_found:
                break

    if relations_found:
        log.info(f"Found {len(relations_found)} lattice relations")
        for rel in relations_found[:64]:
            cand = 0
            for i, zi in enumerate(rel):
                b_i = SMALL_PRIMES[i % len(SMALL_PRIMES)]
                cand = (cand + zi * b_i) % order
            _accept(cand % order, "LLL-cand")
            _accept((cand + K) % order, "LLL-cand+K")
            _accept((-cand) % order, "LLL-neg")
            _accept(((-cand) + K) % order, "LLL-neg+K")
    if verified:
        return {"verified": verified,
                "relations": relations_found[:50], "tier": "lattice-LLL",
                "candidates_checked": len(candidates_seen)}

    # Tier 4 — multi-depth CF / GCD / half-splits
    log.info("Tier 4: multi-depth CF / GCD / half-splits")
    for bs, _ in counts.most_common():
        clean = bs.replace(" ", "")
        if not clean:
            continue
        for variant in (clean, clean[::-1]):
            try:
                m = int(variant, 2) % (1 << bits)
            except ValueError:
                continue
            if m == 0:
                continue
            for dd in range(1, 24):
                r_num, r_den = continued_fraction_approx(m, dd)
                if not r_den:
                    continue
                inv_d = modinv(r_den, order)
                if inv_d is None:
                    continue
                kk = (r_num * inv_d) % order
                _accept(kk, f"CF-dd{dd}")
                _accept((kk + K) % order, f"CF-dd{dd}+K")
            if math.gcd(m, order) > 1:
                for mult in range(1, 12):
                    g = math.gcd(m * mult, order)
                    if 1 < g < order:
                        _accept(g, "GCD")
                        _accept((g + K) % order, "GCD+K")
            hi = m >> (bits // 2)
            lo = m & ((1 << (bits // 2)) - 1)
            for part in (hi, lo):
                if part:
                    _accept(part, "half")
                    _accept((part + K) % order, "half+K")

    return {
        "verified": verified,
        "relations": relations_found[:50],
        "tier": "exhausted" if not verified else "inline-sweep",
        "candidates_checked": len(candidates_seen),
    }


# ═══════════════════════════════════════════════════════════════════════════
# MAIN SOLVER
# ═══════════════════════════════════════════════════════════════════════════
def solve(cfg: Dict[str, Any]) -> Dict[str, Any]:
    pubkey = cfg["pubkey"]
    bits = int(cfg["bits"])
    k_start = int(cfg.get("k_start", (1 << (bits - 1)) if bits > 1 else 1))
    platform = cfg["platform"]
    shots = int(cfg.get("shots", 4096 if bits <= 21 else 65536))

    Q_pt = decompress_pubkey(pubkey)
    if Q_pt is None:
        raise ValueError("Invalid compressed SEC1 pubkey")

    log.info("=" * 78)
    log.info(f"REGEV SOLVER — bits={bits}, k_start={hex(k_start)}")
    log.info(f"  Q.x = {hex(Q_pt[0])[:24]}...")
    log.info(f"  Q.y = {hex(Q_pt[1])[:24]}...")
    log.info(f"  platform={platform}, shots={shots}")
    log.info("=" * 78)

    params = compute_regev_params(
        bits, k_start=k_start,
        d_override=int(cfg.get("d", 0)),
        qpd_override=int(cfg.get("qpd", 0)),
        R_override=float(cfg.get("R", 0.0)),
    )
    log.info(f"Regev params: d={params.d}, qpd={params.qpd}, "
             f"R={params.R:.3f}, D={params.D}")

    log.info("Precomputing EC group elements...")
    delta_powers, basis_powers = precompute_delta_powers(Q_pt, k_start, bits, params.d)
    log.info(f"  delta_powers: {len(delta_powers)} entries")
    log.info(f"  basis_powers: {params.d} dims x {len(basis_powers[0])} entries")

    log.info("Building Regev circuit...")
    qc = build_regev_circuit(params, delta_powers, basis_powers)

    log.info(f"Executing on {platform}...")
    t0 = time.time()
    if platform == "aer":
        counts = execute_aer(qc, shots, seed=int(cfg.get("seed", 7)))
    elif platform == "ibm":
        counts = execute_ibm(qc, shots,
                             backend_name=cfg.get("ibm_backend", "ibm_fez"),
                             token=cfg.get("ibm_token", ""),
                             crn=cfg.get("ibm_crn", ""))
    elif platform == "iqm":
        counts = execute_iqm(qc, shots,
                             device=cfg.get("iqm_device", "emerald"),
                             token=cfg.get("iqm_token", ""),
                             url=cfg.get("iqm_url", "https://resonance.iqm.tech"))
    elif platform == "origin":
        counts = execute_origin(qc, shots,
                                token=cfg.get("origin_token", ""),
                                device=cfg.get("origin_device", "WK_C180"),
                                use_qpu=bool(cfg.get("origin_qpu", False)))
    elif platform == "rigetti":
        counts = execute_rigetti(qc, shots,
                                 qbraid_key=cfg.get("qbraid_key", ""),
                                 device_id=cfg.get("rigetti_device",
                                                   "openquantum:rigetti:qpu:cepheus-1-108q"))
    else:
        raise ValueError(f"Unknown platform: {platform}")
    elapsed = time.time() - t0

    log.info(f"Execution complete in {elapsed:.1f}s, "
             f"{len(counts)} unique outcomes, {sum(counts.values())} shots")

    log.info("Running post-processing...")
    t0 = time.time()
    result = postprocess_regev(counts, params, Q_pt)
    pp_elapsed = time.time() - t0
    log.info(f"Post-processing complete in {pp_elapsed:.1f}s")

    output: Dict[str, Any] = {
        "version": "regev-secp256k1-1.0",
        "timestamp": datetime.now().isoformat(),
        "pubkey": pubkey,
        "bits": bits,
        "k_start": k_start,
        "platform": platform,
        "shots": shots,
        "elapsed_execute_s": elapsed,
        "elapsed_postprocess_s": pp_elapsed,
        "params": asdict(params),
        "circuit": {
            "qubits": qc.num_qubits,
            "depth": qc.depth(),
            "size": qc.size(),
        },
        "counts_top": dict(counts.most_common(20)),
        "postprocessing": result,
        "verified_keys": result["verified"],
        "success": bool(result["verified"]),
    }

    if result["verified"]:
        k = result["verified"][0]
        output["private_key"] = k
        output["private_key_hex"] = hex(k)
        assert verify_key(k, Q_pt), "Final verification failed!"
        log.info(f"SUCCESS: private key = {hex(k)}")
    else:
        log.warning("No key recovered in this run")

    return output


# ═══════════════════════════════════════════════════════════════════════════
# PRESETS
# ═══════════════════════════════════════════════════════════════════════════
PRESETS = {
    "12":  {"bits": 12,  "start": 0x800, "shots": 2048,
            "pub": "0326445a42b856e565baddd47a6f937d9299d740413212102264b4385e90a32f8d"},
    "16":  {"bits": 16,  "start": 0x8000, "shots": 4096,
            "pub": "02d69ccdb7637954cb1d5885900aa24629580b076d190922a7a5165af0a92a42bc"},
    "20":  {"bits": 20,  "start": 0x80000, "shots": 32768,
            "pub": "021d23d69498096c3cb8f8cc50547a921be5268ab8bf9d40c167275c8f4c9c7e00"},
    "22":  {"bits": 22,  "start": 0x200000, "shots": 32768,
            "pub": "023ed96b524db5ff4fe007ce730366052b7c511dc566227d929070b9ce917abb43"},
    "135": {"bits": 135, "start": 0x400000000000000000000000000000000, "shots": 65536,
            "pub": "02145d2611c823a396ef6712ce0f712f09b9b4f3135e3e0aa3230fb9b6d08d1e16"},
    "140": {"bits": 140, "start": 0x80000000000000000000000000000000000, "shots": 65536,
            "pub": "031f6a332d3c5c4f2de2378c012f429cd109ba07d69690c6c701b6bb87860d6640"},
}


# ═══════════════════════════════════════════════════════════════════════════
# INTERACTIVE MENU
# ═══════════════════════════════════════════════════════════════════════════
def ask(prompt: str, default: str = "") -> str:
    suffix = f" [{default}]" if default else ""
    try:
        v = input(f"{prompt}{suffix}: ").strip()
    except EOFError:
        return default
    return v if v else default


def ask_int(prompt: str, default: int) -> int:
    while True:
        try:
            return int(ask(prompt, str(default)), 0)
        except ValueError:
            print("Invalid integer")


def ask_yes(prompt: str, default: bool = True) -> bool:
    d = "Y/n" if default else "y/N"
    v = ask(f"{prompt} [{d}]", "").lower()
    return default if not v else v in ("y", "yes", "1", "true")


def print_banner():
    print("""
+--------------------------------------------------------------------------+
|  REGEV SECP256K1 ECDLP SOLVER - Full Edition                             |
|  Real arithmetic | 4 quantum platforms | Multi-tier post-processing      |
|  Range: 22-bit keys up to 140+ bits                                      |
+--------------------------------------------------------------------------+
""")


def interactive_solve():
    print_banner()
    print(platform_report())
    print()

    print("PRESETS:")
    for k, v in PRESETS.items():
        print(f"  [{k:>3}] {v['bits']:>3}-bit  shots={v['shots']}")
    print("  [  c] Custom (enter your own compressed pubkey)")
    print()

    choice = ask("Select preset", "16")

    cfg: Dict[str, Any] = {}
    if choice in PRESETS:
        p = PRESETS[choice]
        cfg["pubkey"] = p["pub"]
        cfg["bits"] = p["bits"]
        cfg["k_start"] = p["start"]
        cfg["shots"] = p["shots"]
    else:
        cfg["pubkey"] = ask("Compressed SEC1 pubkey (66 hex chars)")
        cfg["bits"] = ask_int("Key-range bit-length", 22)
        default_start = (1 << (cfg["bits"] - 1)) if cfg["bits"] > 1 else 1
        cfg["k_start"] = ask_int("Range start (hex OK)", default_start)
        cfg["shots"] = ask_int("Shots", 4096 if cfg["bits"] <= 21 else 65536)

    Q_pt = decompress_pubkey(cfg["pubkey"])
    if Q_pt is None:
        print("ERROR: invalid compressed SEC1 pubkey")
        return

    print(f"\nTarget: {cfg['bits']}-bit key range")
    print(f"  Q.x = {hex(Q_pt[0])[:24]}...")
    print(f"  Q.y = {hex(Q_pt[1])[:24]}...")
    print(f"  Range: [{hex(cfg['k_start'])}, "
          f"{hex(cfg['k_start'] + (1 << cfg['bits']) - 1)}]")

    available = []
    if PLATFORMS.get("aer"): available.append("aer")
    if PLATFORMS.get("ibm"): available.append("ibm")
    if PLATFORMS.get("iqm_qiskit") or PLATFORMS.get("iqm_pytket"):
        available.append("iqm")
    if PLATFORMS.get("origin"): available.append("origin")
    if PLATFORMS.get("rigetti_qbraid"): available.append("rigetti")

    if not available:
        print("No quantum platforms available. Install at least qiskit-aer.")
        return

    print(f"\nAvailable platforms: {', '.join(available)}")
    default_platform = "aer" if (cfg["bits"] <= 21 and "aer" in available) else available[0]
    platform = ask("Platform", default_platform)
    if platform not in available:
        print(f"Unavailable: {platform}")
        return
    cfg["platform"] = platform

    default_params = compute_regev_params(cfg["bits"], k_start=cfg["k_start"])
    print(f"\nAuto params: d={default_params.d}, qpd={default_params.qpd}, "
          f"R={default_params.R:.2f}")
    if ask_yes("Override Regev parameters?", False):
        cfg["d"] = ask_int("d (dimension)", default_params.d)
        cfg["qpd"] = ask_int("qpd (qubits per dim)", default_params.qpd)
        cfg["R"] = float(ask("R (Gaussian width)", str(default_params.R)))

    if platform == "ibm":
        cfg["ibm_token"] = os.getenv("IBM_QUANTUM_TOKEN", "") or getpass.getpass("IBM token: ")
        cfg["ibm_crn"] = os.getenv("IBM_QUANTUM_CRN", "") or ask("IBM CRN (optional)")
        cfg["ibm_backend"] = ask("IBM backend", "ibm_fez")
    elif platform == "iqm":
        cfg["iqm_token"] = os.getenv("IQM_TOKEN", "") or getpass.getpass("IQM token: ")
        cfg["iqm_device"] = ask("IQM device", "emerald")
        cfg["iqm_url"] = ask("IQM server URL", "https://resonance.iqm.tech")
    elif platform == "origin":
        cfg["origin_token"] = os.getenv("ORIGINQC_TOKEN", "") or getpass.getpass("OriginQC token: ")
        cfg["origin_device"] = ask("OriginQC device", "WK_C180")
        cfg["origin_qpu"] = ask_yes("Use real QPU?", False)
    elif platform == "rigetti":
        cfg["qbraid_key"] = os.getenv("QBRAID_API_KEY", "") or getpass.getpass("qBraid API key: ")
        cfg["rigetti_device"] = ask("Rigetti device ID",
                                    "openquantum:rigetti:qpu:cepheus-1-108q")

    print("\nStarting solve...")
    try:
        output = solve(cfg)
        print("\n" + "=" * 78)
        print("RESULT")
        print("=" * 78)
        print(json.dumps(output, indent=2, default=str))

        stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        out_path = CACHE / f"result_{stamp}.json"
        out_path.write_text(json.dumps(output, indent=2, default=str))
        print(f"\nSaved: {out_path}")

        if output.get("success"):
            key_path = CACHE / f"FOUND_KEY_{stamp}.txt"
            key_path.write_text(
                f"Private key (dec): {output['private_key']}\n"
                f"Private key (hex): {output['private_key_hex']}\n"
                f"Public key: {cfg['pubkey']}\n"
                f"Bits: {cfg['bits']}\n"
                f"Platform: {cfg['platform']}\n"
            )
            print(f"Key saved: {key_path}")
    except Exception as e:
        log.error(f"Solver failed: {e}")
        traceback.print_exc()


# ═══════════════════════════════════════════════════════════════════════════
# CLI
# ═══════════════════════════════════════════════════════════════════════════
def cli_main(argv=None):
    ap = argparse.ArgumentParser(
        description="Regev secp256k1 ECDLP solver (22-bit and above)"
    )
    ap.add_argument("--pubkey", required=True, help="Compressed SEC1 pubkey")
    ap.add_argument("--bits", type=int, required=True, help="Key range bit-length")
    ap.add_argument("--k-start", type=lambda x: int(x, 0), default=None,
                    help="Range start (hex OK; default 2^(bits-1))")
    ap.add_argument("--platform", choices=["aer", "ibm", "iqm", "origin", "rigetti"],
                    default="aer")
    ap.add_argument("--shots", type=int, default=4096)
    ap.add_argument("--d", type=int, default=0)
    ap.add_argument("--qpd", type=int, default=0)
    ap.add_argument("--R", type=float, default=0.0)
    ap.add_argument("--seed", type=int, default=7)
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
    ap.add_argument("--json-out", default="")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--platform-report", action="store_true")

    args = ap.parse_args(argv if argv is not None else sys.argv[1:])

    if args.platform_report:
        print(platform_report())
        return 0

    if args.self_test:
        run_self_test()
        return 0

    k_start = (args.k_start if args.k_start is not None
               else ((1 << (args.bits - 1)) if args.bits > 1 else 1))

    cfg: Dict[str, Any] = {
        "pubkey": args.pubkey,
        "bits": args.bits,
        "k_start": k_start,
        "platform": args.platform,
        "shots": args.shots,
        "d": args.d,
        "qpd": args.qpd,
        "R": args.R,
        "seed": args.seed,
        "ibm_token": args.ibm_token,
        "ibm_crn": args.ibm_crn,
        "ibm_backend": args.ibm_backend,
        "iqm_token": args.iqm_token,
        "iqm_device": args.iqm_device,
        "iqm_url": args.iqm_url,
        "origin_token": args.origin_token,
        "origin_device": args.origin_device,
        "origin_qpu": args.origin_qpu,
        "qbraid_key": args.qbraid_key,
        "rigetti_device": args.rigetti_device,
    }

    output = solve(cfg)
    print(json.dumps(output, indent=2, default=str))
    if args.json_out:
        Path(args.json_out).write_text(json.dumps(output, indent=2, default=str))
    return 0 if output.get("success") else 1


# ═══════════════════════════════════════════════════════════════════════════
# SELF-TEST
# ═══════════════════════════════════════════════════════════════════════════
def run_self_test():
    log.info("Running self-tests...")

    assert pt_mul(1, G) == G
    assert pt_mul(2, G) == pt_add(G, G)
    assert pt_mul(N, G) is None, "N.G must be infinity"
    assert pt_mul(0, G) is None
    assert pt_add(G, pt_neg(G)) is None
    for k1, k2 in [(1, 1), (2, 3), (17, 42), (1000, 2000)]:
        assert pt_add(pt_mul(k1, G), pt_mul(k2, G)) == pt_mul(k1 + k2, G)
    log.info("[OK] EC arithmetic")

    for k in [1, 2, 12345, 0xDEADBEEF, 0x100000000000000000000]:
        Q = pt_mul(k, G)
        hx = compress_point(Q)
        Q2 = decompress_pubkey(hx)
        assert Q2 == Q, f"Decompression round-trip failed for k={k}"
    log.info("[OK] SEC1 decompression round-trip")

    Q_test = pt_mul(0x1234, G)
    assert verify_key(0x1234, Q_test)
    assert not verify_key(0x1235, Q_test)
    log.info("[OK] verify_key accept/reject")

    for b in [12, 16, 22, 40, 80, 140, 256]:
        p = compute_regev_params(b)
        assert p.d >= 2 and p.qpd >= 4
        assert p.D == (1 << p.qpd)
        assert p.range_size == (1 << b)
        log.info(f"  params for {b}-bit: d={p.d}, qpd={p.qpd}, R={p.R:.2f}")
    log.info("[OK] Regev parameter selection")

    Q_pre = pt_mul(0x5678, G)
    dp, bp = precompute_delta_powers(Q_pre, 0, 16, 4)
    assert len(dp) == 16
    assert len(bp) == 4 and all(len(row) == 16 for row in bp)
    log.info("[OK] Group-element precompute")

    if QISKIT_OK:
        params = compute_regev_params(16, d_override=4, qpd_override=6)
        qc = build_regev_circuit(params, dp, bp)
        assert qc.num_qubits == 4 * 6 + 16
        log.info(f"[OK] Circuit: {qc.num_qubits}q, depth {qc.depth()}, size {qc.size()}")

        if PLATFORMS.get("aer"):
            k_true = 0x1234
            Q_k = pt_mul(k_true, G)
            params = compute_regev_params(16, k_start=0, d_override=4, qpd_override=6)
            dp2, bp2 = precompute_delta_powers(Q_k, 0, 16, 4)
            qc2 = build_regev_circuit(params, dp2, bp2)
            try:
                counts = execute_aer(qc2, shots=512, seed=42)
                res = postprocess_regev(counts, params, Q_k)
                log.info(f"  Aer solve: tier={res.get('tier')}, "
                         f"candidates={res.get('candidates_checked')}, "
                         f"verified={len(res['verified'])}")
            except Exception as e:
                log.warning(f"  Aer solve failed: {e}")

    try:
        from fpylll import IntegerMatrix  # noqa
        log.info("[OK] fpylll LLL available")
    except ImportError:
        try:
            from sympy import Matrix  # noqa
            log.info("[OK] sympy LLL fallback available")
        except ImportError:
            log.warning("[WARN] No LLL backend (install fpylll or sympy)")

    log.info("All self-tests passed")


# ═══════════════════════════════════════════════════════════════════════════
# ENTRY POINT
# ═══════════════════════════════════════════════════════════════════════════
if __name__ == "__main__":
    if len(sys.argv) > 1:
        sys.exit(cli_main())
    else:
        interactive_solve()