"""Uniform global Riesz-energy certificate, rebuilt from scratch on each run.
There are no checkpoint files, stored approximate solutions, or cached reports
used as verification inputs. The frozen JSON numbers specify exact rationals.
"""

from pathlib import Path
import sys, json, time, math, os
import mpmath as mp, numpy as np
from taylor_models import TM, ORDER, iv
from matrix_models import MT, toI
from ipoly import IP, prepare_right
from exact_mm import prepared_left
from fast_interval import mm, absI, norm
from interval_arithmetic import I, down, up, sqrt_integer
import build_models as b

v = b.v


def spectral_upper(M):
    # A numerical eigenbasis is only a rational witness. Both its near-orthogonality
    # and the transformed norm are independently bounded with interval arithmetic.
    mid = M.lo / 2 + M.hi / 2
    _, Qn = np.linalg.eigh((mid + mid.T) / 2)
    Q = I(Qn)
    eps = norm(mm(Q.T, Q) - I(np.eye(Qn.shape[0])))
    if not eps < 1:
        raise ArithmeticError("Spectral witness not invertible")
    transformed = mm(mm(Q.T, M), Q)
    return float((I(norm(transformed)) / (1 - I(eps))).hi)


def approximate_solve_model(T, r):
    # Numerical Taylor polynomials are only proposals: the complete residuals,
    # including all low-order coefficients and truncation errors, are enclosed.
    tt = [cc.lo / 2 + cc.hi / 2 for cc in T.c]
    rr = [cc.lo / 2 + cc.hi / 2 for cc in r.c]
    pi = [np.linalg.inv(tt[0])]
    zz = [pi[0] @ rr[0]]
    for k in range(1, ORDER + 1):
        pi.append(
            -pi[0]
            @ sum((tt[i] @ pi[k - i] for i in range(1, k + 1)), np.zeros_like(pi[0]))
        )
        zz.append(
            pi[0]
            @ (
                rr[k]
                - sum(
                    (tt[i] @ zz[k - i] for i in range(1, k + 1)), np.zeros_like(zz[0])
                )
            )
        )
    PP = IP([I(c) for c in pi])
    ZZ = IP([I(c) for c in zz])
    identity = IP.const(I(np.eye(pi[0].shape[0])))
    Res = identity.add(T.multiply(PP).negative())
    q = norm(Res.bound())
    print(
        "Polynomial inverse full residual",
        q,
        "tail",
        norm(Res.e),
        "inverse norm",
        norm(PP.poly_bound()),
        flush=True,
    )
    if not q < 1:
        raise ArithmeticError(("Polynomial inverse failed", q))
    resid = r.add(T.multiply(ZZ).negative())
    # Componentwise Neumann bounds: T^{-1}=P(I-(I-TP))^{-1}.
    # If |I-TP|<=B and |r-TZ|<=rho, then delta=(I-B)^{-1}rho
    # is dominated by the initial uniform bound.  Each outward recurrence
    # delta <- rho+B delta remains an upper bound; finite iteration is enough.
    B = Res.bound()
    rho = resid.bound()
    u = float((I(norm(rho)) / (1 - I(q))).hi)
    delta = I(np.full_like(rho.lo, u))
    for _ in range(12):
        delta = I((rho + mm(B, delta)).hi)
    component = I(mm(PP.poly_bound(), delta).hi)
    scalar = float((I(norm(PP.poly_bound())) / (1 - I(q)) * I(norm(rho))).hi)
    component = I(np.minimum(component.hi, scalar))
    error = norm(component)
    print(
        "Polynomial solution full residual",
        norm(rho),
        "component solution error",
        error,
        "old uniform bound",
        scalar,
        flush=True,
    )
    result = IP(ZZ.c, component)
    result.inverse_residual_upper = q
    result.inverse_polynomial_norm_upper = norm(PP.poly_bound())
    result.solution_residual_upper = norm(resid.bound())
    result.solution_error_upper = error
    return result


def coefficient_model(data, bases, rows, inds):
    blocks = []
    rt = sqrt_integer(2)
    for dat, B, ii in zip(data, bases, inds):
        print("Coefficient model", dat["name"], time.time(), flush=True)
        assert np.array_equal(
            dat["raw"], np.swapaxes(dat["raw"], -1, -2)
        ), "nonsymmetric raw matrix"
        if np.max(np.abs(dat["raw"])) > 2**53:
            raise ArithmeticError("Raw integer not exactly representable")
        raw = I(dat["raw"][rows]) / dat["den"]
        ra = absI(raw)
        # Only pivot rows vary with the exponent.  The other rows are exact
        # constant rows, explicitly restored by build_models after multiplication.
        active = B.active_rows
        rv = raw[:, :, active]
        r2 = raw[:, active, :][:, :, active]
        av = ra[:, :, active]
        a2 = ra[:, active, :][:, :, active]
        bb = [B.c[k][active, :] for k in range(ORDER + 1)]
        rb0 = mm(raw, B.c[0])
        rbv = [None] + [mm(rv, bb[k]) for k in range(1, ORDER + 1)]
        rbb = [None] + [mm(r2, bb[k]) for k in range(1, ORDER + 1)]
        cc = [mm(B.c[0].T, rb0)]
        for k in range(1, ORDER + 1):
            z = mm(B.c[0].T, rbv[k])
            z = z + I(np.swapaxes(z.lo, -1, -2), np.swapaxes(z.hi, -1, -2))
            for i in range(1, k // 2 + 1):
                j = k - i
                zz = mm(bb[i].T, rbb[j])
                if i != j:
                    zz = zz + I(np.swapaxes(zz.lo, -1, -2), np.swapaxes(zz.hi, -1, -2))
                z = z + zz
            cc.append(z)
        # Terms above ORDER have both factors of positive order and thus only
        # involve pivot rows. All basis remainders also vanish on free rows.
        tail = I(np.zeros_like(cc[0].lo))
        abb = [absI(x) for x in bb]
        arB = [None] + [mm(a2, abb[j]) for j in range(1, ORDER + 1)]
        for i in range(1, ORDER + 1):
            rsum = I(np.zeros_like(arB[1].lo))
            for j in range(ORDER + 1 - i, ORDER + 1):
                rsum = rsum + arB[j]
            tail = tail + mm(abb[i].T, rsum)
        eps = B.e[active, :]
        vp = I(np.zeros_like(eps.lo))
        for j in range(1, ORDER + 1):
            vp = vp + abb[j]
        tmp = mm(absI(B.c[0]).T, mm(av, eps)) + mm(vp.T, mm(a2, eps))
        tail = (
            tail
            + tmp
            + I(np.swapaxes(tmp.lo, -1, -2), np.swapaxes(tmp.hi, -1, -2))
            + mm(eps.T, mm(a2, eps))
        )

        def vec(z):
            cols = [z[:, i, j] * (1 if i == j else rt) for i, j in ii]
            return I(
                np.column_stack([x.lo for x in cols]),
                np.column_stack([x.hi for x in cols]),
            )

        blocks.append(IP([vec(c) for c in cc], absI(vec(tail))))

    def concat(j):
        return I(
            np.column_stack([BB.c[j].lo for BB in blocks]),
            np.column_stack([BB.c[j].hi for BB in blocks]),
        )

    E = I(
        np.column_stack([BB.e.lo for BB in blocks]),
        np.column_stack([BB.e.hi for BB in blocks]),
    )
    return IP([concat(j) for j in range(ORDER + 1)], E)


def correction_models_streamed(data, bases, rows, inds, slices, C, w0, targetM):
    """Enclose T=A_R C and r=b_R-A_R w0 without storing all columns.
 All operations reuse the same outward polynomial products. Row/block
 partitions are exact linear decompositions, not approximations.
 """
    nrows = len(rows)
    chunk = int(os.environ.get("N8_ROW_CHUNK", "12"))
    if not 1 <= chunk <= 64:
        raise ValueError("Invalid row chunk")
    tc = [I(np.zeros((nrows, nrows))) for _ in range(ORDER + 1)]
    te = I(np.zeros((nrows, nrows)))
    rc = [cc for cc in targetM.c]
    re = targetM.e
    for dat, B, ii, sl in zip(data, bases, inds, slices):
        cb = C[sl, :]
        x0 = I(w0[sl, None])
        right_c, right_x = prepare_right(cb), prepare_right(x0)
        for start in range(0, nrows, chunk):
            stop = min(start + chunk, nrows)
            jj = slice(start, stop)
            coeff = coefficient_model([dat], [B], rows[jj], [ii])
            tt = right_c(coeff)
            rr = right_x(coeff)
            for k in range(ORDER + 1):
                tc[k][jj, :] = tc[k][jj, :] + tt.c[k]
                rc[k][jj, :] = rc[k][jj, :] - rr.c[k]
            te[jj, :] = te[jj, :] + tt.e
            re[jj, :] = re[jj, :] + rr.e
        del right_c, right_x
    return IP(tc, te), IP(rc, re)


def unpack(IPw, ii, sl):
    m = max(j for i, j in ii) + 1
    c = []
    ee = I(np.zeros((m, m)))
    rt = sqrt_integer(2)
    for k in range(ORDER + 1):
        z = I(np.zeros((m, m)))
        for idx, (i, j) in enumerate(ii):
            z[i, j] = z[j, i] = IPw.c[k][sl.start + idx, 0] / (1 if i == j else rt)
        c.append(z)
    for idx, (i, j) in enumerate(ii):
        ee[i, j] = ee[j, i] = IPw.e[sl.start + idx, 0] / (1 if i == j else rt)
    return IP(c, absI(ee))


def verify(center, width, *, record, out=None, minorant="general"):
    st = time.time()
    work = Path(__file__).parent
    mp.mp.dps = 100
    S, A, root, rec, data, bases, target = b.build(center, width, record, minorant)
    if (
        len(data) != v.D + 3
        or len(bases) != v.D + 3
        or len(rec["PSD_preconditioners"]) != v.D + 3
    ):
        raise ArithmeticError("Wrong number of matrix blocks")
    inds, slices = v.vectorization_layout([B.mp0 for B in bases])
    rows = np.array(rec["rows"])
    x = np.array(rec["svec_center"])
    C = I(rec["right_inverse"])
    nvars = sum(len(ii) for ii in inds)
    nrows = len(v.EXPS) - 2
    if x.shape != (nvars,) or C.lo.shape != (nvars, nrows):
        raise ArithmeticError("Wrong witness coordinate dimensions")
    if not np.all(np.isfinite(x)):
        raise ArithmeticError("Nonfinite matrix center")
    if (
        len(rows) != nrows
        or len(set(rows.tolist())) != nrows
        or min(rows) < 0
        or max(rows) >= len(v.EXPS)
    ):
        raise ArithmeticError("Invalid independent-row selection")
    targetM = IP.fromMT(target).slice(list(rows), [0])
    mode = os.environ.get("N8_COEFFICIENT_MODE", "streamed")
    row_workers = int(os.environ.get("N8_ROW_WORKERS", "1"))
    if not 1 <= row_workers <= 6:
        raise ValueError("Invalid row worker count")
    row_workers = (row_workers if v.D == 10 else min(3, row_workers) if v.D == 9 else 1) if sys.platform.startswith("linux") else 1
    if mode == "streamed":
        if row_workers > 1:
            from parallel_chunks import correction_models_parallel
            T, r = correction_models_parallel(
                data, bases, rows, inds, slices, C, x, targetM, workers=row_workers
            )
        else:
            T, r = correction_models_streamed(
                data, bases, rows, inds, slices, C, x, targetM
            )
    elif mode == "full":
        AM = coefficient_model(data, bases, rows, inds)
        r = targetM.add(AM.right(I(x[:, None])).negative())
        T = AM.right(C)
    else:
        raise ValueError("Unknown coefficient mode")
    # Recompute the constant polynomial coefficient of this residual at high
    # precision. This encloses the SAME coefficient, using the stored interval
    # constant coefficients of every basis and of the target. The uniform
    # Taylor remainders remain unchanged and include the root-model error.
    hp = v.residual_high_precision(
        data,
        [BB.mp0 for BB in bases],
        x,
        inds,
        slices,
        target.c[0],
        rec["basis_records"],
    )
    r.c[0] = toI(iv.matrix([[hp[int(j), 0]] for j in rows]))
    # Optional rational left preconditioning changes selected coefficient
    # coordinates, not their exact identity. Invertibility of L A_R C itself
    # proves the square left factor invertible as well as rank(A_R)=nrows.
    left = rec.get("left_preconditioner")
    if left is not None:
        L = I(left)
        if L.lo.shape != (nrows, nrows) or not np.all(np.isfinite(L.lo)):
            raise ArithmeticError("Invalid left preconditioner")
        T = IP([mm(L, cc) for cc in T.c], mm(absI(L), T.e))
        r = IP([mm(L, cc) for cc in r.c], mm(absI(L), r.e))
        LM = iv.matrix([[iv.mpf(float(z)) for z in row] for row in left])
        r.c[0] = toI(LM * iv.matrix([[hp[int(j), 0]] for j in rows]))

    # The refined coefficient and the remaining binary64 coefficients enclose
    # the exact residual; no approximate equality or midpoint residual is assumed.
    print("Residual model upper", norm(r.bound()), "remainder", norm(r.e), flush=True)
    z = approximate_solve_model(T, r)
    left_c = prepared_left(C)
    ww = IP([left_c(coef) for coef in z.c], mm(absI(C), z.e))
    del left_c
    ww.c[0] = ww.c[0] + I(x[:, None])
    deltas = []
    for name, ii, sl, pp in zip(
        [d["name"] for d in data], inds, slices, rec["PSD_preconditioners"]
    ):
        W = unpack(ww, ii, sl)
        P = I(pp)
        if P.lo.ndim != 2 or P.lo.shape[0] != P.lo.shape[1] or P.lo.shape[1] != W.c[0].lo.shape[0]:
            raise ArithmeticError("Invalid square PSD preconditioner")
        coeff = [mm(mm(P, c), P.T) for c in W.c]
        coeff[0] = coeff[0] - I(np.eye(P.lo.shape[0]))
        err = mm(mm(absI(P), W.e), absI(P).T)
        Bnd = err
        for c in coeff:
            Bnd = Bnd + absI(c)
        inf_delta = norm(Bnd)
        spec = I(norm(err))
        for ck in coeff:
            spec = spec + I(spectral_upper(ck))
        delta = min(inf_delta, float(spec.hi))
        deltas.append(delta)
        print(
            "Uniform positive-definiteness",
            name,
            delta,
            "entrywise bound",
            inf_delta,
            "remainder",
            norm(err),
            flush=True,
        )
    if not max(deltas) < 1:
        raise ArithmeticError(("PSD uniform test failed", deltas))
    # Equality: contact nodes and opposite pairs.
    ns = [A, 2 * A - 1, -A + (1 - A) / iv.sqrt(2), -A - (1 - A) / iv.sqrt(2)]
    for n in ns:
        if 0 in n.interval():
            raise ArithmeticError("zero contact node")
    for i in range(4):
        for j in range(i + 1, 4):
            if 0 in (ns[i] - ns[j]).interval() or 0 in (ns[i] + ns[j]).interval():
                raise ArithmeticError("distinct/opposite condition")
    if not (3 * A - 1).interval().b < 0:
        raise ArithmeticError("rank dependency condition")
    exclusions = []
    for tt in [(0, 0, 0), (0, 0, 2), (0, 0, 3)]:
        es = data[v.D]["monoms"]
        xyz = [ns[j] for j in tt]
        vals = IP.fromMT(
            MT.from_scalars(
                [[xyz[0] ** e[0] * xyz[1] ** e[1] * xyz[2] ** e[2]] for e in es]
            )
        )
        outz = bases[v.D].T().multiply(vals)
        rad = outz.e
        for ck in outz.c[1:]:
            rad = rad + absI(ck)
        rr = outz.c[0] + I(-rad.hi, rad.hi)
        idx = np.argmax(np.maximum(rr.lo[:, 0], -rr.hi[:, 0]))
        lower = max(rr.lo[idx, 0], -rr.hi[idx, 0])
        if not lower > 0:
            raise ArithmeticError(("forbidden triple", tt))
        exclusions.append(
            {
                "type": tt,
                "component": int(idx),
                "absolute_lower_bound": float(down(lower)),
            }
        )
    # N0 change-of-basis is a fixed rational matrix: check invertibility.
    J = I(rec["basis_records"][0]["change_of_basis"])
    Ci = I(np.linalg.inv((J.lo + J.hi) / 2))
    qJ = norm(I(np.eye(J.lo.shape[0])) - mm(Ci, J))
    if not qJ < 1:
        raise ArithmeticError("F0 basis change singular")
    report = {
        "target_multiplier": rec["_target_multiplier"],
        "hermite_multiplicities": rec["_hermite_multiplicities"],
        "potential_evaluation": rec["_potential_evaluation"],
        "left_preconditioned": left is not None,
        "coefficient_mode": mode,
        "row_workers": row_workers,
        "degree": 2 * v.D,
        "auxiliary_nodes": rec["auxiliary_nodes"],
        "coefficient_rows": len(v.EXPS),
        "selected_rows": nrows,
        "svec_dimension": nvars,
        "center": center,
        "halfwidth": width,
        "order": ORDER,
        "minorant": minorant,
        "root": root,
        "PSD_uniform_errors": deltas,
        "forbidden_triples": exclusions,
        "F0_basis_change_inverse_error": qJ,
        "right_inverse_uniform_residual": z.inverse_residual_upper,
        "inverse_polynomial_norm_upper": z.inverse_polynomial_norm_upper,
        "solution_residual_upper": z.solution_residual_upper,
        "solution_error_upper": z.solution_error_upper,
        "matrix_bound_type": "uniform symmetric operator-norm bound (minimum of proved entrywise and congruence estimates)",
        "elapsed_seconds": time.time() - st,
        "passed": True,
        "scope": "Global energy bound and uniqueness for every nonnegative exponent in the stated closed interval; logarithmic normalization at zero.",
    }
    if out:
        Path(out).write_text(json.dumps(report, indent=2))
    print(json.dumps(report, indent=2), flush=True)
    return report
