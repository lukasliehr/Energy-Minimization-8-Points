import sys, json, math, time, itertools, os
from pathlib import Path
import numpy as np, mpmath as mp
from taylor_models import (
    TM,
    ORDER,
    iv,
    candidate_model,
    normalized_phi,
    potential_evaluation_mode,
)
from matrix_models import MT, right_constant, toI, solve_model
from ipoly import IP
from interval_arithmetic import I

import structure as v
from hermite import hermite_coefficients

ONE_TM = TM.const(1)
EVAL_CACHE = {}


def eval_tm(poly, nodes):
    key = tuple(id(z) for z in nodes)
    if key not in EVAL_CACHE:
        EVAL_CACHE[key] = ([[z**j for j in range(2 * v.D + 1)] for z in nodes], {})
    powers, cache = EVAL_CACHE[key]
    out = TM.const(0)
    for e, c in poly.items():
        if e not in cache:
            val = TM.const(1)
            for k, j in enumerate(e):
                if j:
                    val = val * powers[k][j]
            cache[e] = val
        out = out + cache[e] * c
    return out


def moment_entry(poly, k, nodes):
    val = TM.const(8 if k == 0 else 0)
    for tt, c in zip(v.TRIP_TYPES, v.TRIP_COUNTS):
        val = val + eval_tm(poly, [nodes[x] for x in tt]) * c
    for t, c in zip(nodes, v.PAIR_COUNTS):
        val = val + eval_tm(poly, [t, t, ONE_TM]) * c
    return val


def build(center, width, record, minorant):
    if minorant not in ("general", "original", "far4", "far6"):
        raise ValueError("Unknown Hermite profile")
    EVAL_CACHE.clear()
    start = time.time()
    S, A, rootinfo = candidate_model(center, width)
    print("Root model", rootinfo, flush=True)
    rec = dict(record)
    data = v.raw_data()
    if (
        rec.get("degree") != 2 * v.D
        or len(rec["basis_records"]) != v.D + 3
        or [r["name"] for r in rec["basis_records"]] != [d["name"] for d in data]
    ):
        raise ArithmeticError("Invalid basis block order")
    nodes = [A, 2 * A - 1, -A + (1 - A) / iv.sqrt(2), -A - (1 - A) / iv.sqrt(2)]
    bases = []
    for dat, r in zip(data, rec["basis_records"]):
        print("Basis model", dat["name"], "elapsed", time.time() - start, flush=True)
        if dat["name"].startswith("F"):
            m = dat["raw"].shape[1]
            p = r["pivot"]
            free = r["free"]
            if not 0 <= p < m or sorted(free) != [i for i in range(m) if i != p]:
                raise ArithmeticError("Invalid moment-kernel indices")
            pp = moment_entry(dat["S6"][p][p], dat["k"], nodes)
            if not pp.interval().a > 0:
                raise ArithmeticError("moment pivot not positive")
            M = [[TM.const(int(i == f)) for f in free] for i in range(m)]
            for j, f in enumerate(free):
                M[p][j] = -moment_entry(dat["S6"][p][f], dat["k"], nodes) / pp
            B = MT.from_scalars(M)
        else:
            es = dat["monoms"]
            p = r["pivots"]
            free = r["free"]
            m = len(es)
            if (
                len(p) != 21
                or len(set(p)) != 21
                or any(j < 0 or j >= m for j in p)
                or sorted(free) != [j for j in range(m) if j not in p]
            ):
                raise ArithmeticError("Invalid evaluation-kernel indices")
            nodepowers = [[t**j for j in range(v.D + 1)] for t in nodes]
            M = [
                [
                    nodepowers[tt[0]][e[0]]
                    * nodepowers[tt[1]][e[1]]
                    * nodepowers[tt[2]][e[2]]
                    for e in es
                ]
                for tt in v.TRIP_ALL
            ]
            E = IP.fromMT(MT.from_scalars(M))
            rows = list(range(21))
            print("Evaluation built", time.time() - start, flush=True)
            T = E.slice(rows, p).inverse().multiply(E.slice(rows, free)).negative()
            print("Kernel solve complete", time.time() - start, flush=True)
            c = [I(np.zeros((m, len(free)))) for _ in range(ORDER + 1)]
            err = I(np.zeros((m, len(free))))
            mp0 = iv.matrix(m, len(free))
            for j, f in enumerate(free):
                c[0][f, j] = 1
                mp0[f, j] = 1
            for i, pp in enumerate(p):
                for j in range(len(free)):
                    for k in range(ORDER + 1):
                        c[k][pp, j] = T.c[k][i, j]
                    err[pp, j] = T.e[i, j]
                    mp0[pp, j] = T.mp0[i, j]
            B = IP(c, err, mp0)
        J = iv.matrix([[iv.mpf(float(z)) for z in row] for row in r["change_of_basis"]])
        if J.rows != len(r["free"]) or J.cols != len(r["free"]):
            raise ArithmeticError("Invalid basis-change dimensions")
        if isinstance(B, MT):
            B = IP.fromMT(B)
        B = B.right(toI(J), J)
        # Free rows of the exact evaluation/moment kernel are constant rows of J.
        # Their positive-order Taylor coefficients and remainders are exactly zero.
        free = r["free"]
        active = [r["pivot"]] if dat["name"].startswith("F") else r["pivots"]
        for j, f in enumerate(free):
            B.c[0][f, :] = I(np.asarray(r["change_of_basis"][j], dtype=float))
            for k in range(1, ORDER + 1):
                B.c[k][f, :] = I(np.zeros(len(free)))
            B.e[f, :] = I(np.zeros(len(free)))
        B.active_rows = list(active)
        bases.append(B)
        print("Basis error", float(np.max(B.e.hi)), flush=True)
    if minorant == "general":
        tags = rec["auxiliary_nodes"]
        if len(tags) != v.D - 4 or any(t not in ["A", "B", "C", "D"] for t in tags):
            raise ArithmeticError("Invalid higher degree profile")
        mult = [2 + 2 * tags.count(t) for t in "ABCD"]
        endpoint = 1
    else:
        if v.D != 6:
            raise ArithmeticError("Legacy profiles require degree12")
        tags = {"original": [], "far4": ["B", "D"], "far6": ["B", "B"]}[minorant]
        mult = [2 + 2 * tags.count(t) for t in "ABCD"]
        endpoint = 5 if minorant == "original" else 1
    rec["auxiliary_nodes"] = tags
    rec["_hermite_multiplicities"] = {**dict(zip("ABCD", mult)), "minus_one": endpoint}
    rec["_potential_evaluation"] = potential_evaluation_mode(S)
    if sum(mult) + endpoint != 2 * v.D + 1:
        raise ArithmeticError("Wrong interpolation dimension")
    hc = hermite_coefficients(S, nodes, mult, endpoint)
    print("Hermite Taylor remainder", float(max(x.e.b for x in hc)), flush=True)
    energy = sum(
        [normalized_phi(S, t) * c for t, c in zip(nodes, v.PAIR_COUNTS)], TM.const(0)
    )
    target = []
    for e in v.EXPS:
        if e == (0, 0, 0):
            val = hc[0] - energy / 28
        elif e[0] == e[1] == 0:
            val = hc[e[2]] / 3
        else:
            val = TM.const(0)
        target.append([val])
    # Multiplication by this strictly positive factor does not change the
    # polynomial energy inequality. It equals one at the cell center.
    balance_mode = os.environ.get("N8_TARGET_BALANCE", "unit")
    if balance_mode == "unit":
        balance = TM.const(1)
        rec["_target_multiplier"] = "1"
    elif balance_mode == "riesz":
        cc = iv.mpf(center)
        if not cc.a > 0 or not S.interval().a > 0:
            raise ArithmeticError("Balanced target requires a positive cell")
        balance = (S / cc) * (((S - cc) / 2) * iv.log(iv.mpf(3) / 2)).exp()
        rec["_target_multiplier"] = "(s/center)*(3/2)^((s-center)/2)"
    else:
        raise ArithmeticError("Unknown target balance")
    target = [[balance * row[0]] for row in target]
    print(
        "Built target models", balance_mode, "elapsed", time.time() - start, flush=True
    )
    return S, A, rootinfo, rec, data, bases, MT.from_scalars(target)

