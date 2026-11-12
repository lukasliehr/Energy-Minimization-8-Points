# Eight points on S²: the negative-exponent extension

This package extends the [nonnegative-exponent computation](../Nonnegative_s)
to **−2 < s ≤ 0** for the normalized potential

    φ_s(t) = ((2−2t)^(−s/2) − 1)/s,
    φ_0(t) = −log(2−2t)/2,

where `t` is the inner product. For `s ≠ 0`, adding the constant `1/s` per pair
recovers the Riesz kernel `|x−y|^(−s)/s` without changing the minimizers. The
minimizer is the height-optimized square antiprism, unique up to O(3) and relabeling.

## Result of this computation

All five fresh uniform cell checks passed. Their exact rational parameter union
is `[0,1]`, in the auxiliary parameter `q=(s+2)/2`:

| q interval | Original s interval | Maximum certified PSD error (rounded up) |
|---|---|---:|
| [0, 1/5] | (−2, −8/5] for the Riesz inference | 0.613964 |
| [1/5, 2/5] | [−8/5, −6/5] | 0.619303 |
| [2/5, 3/5] | [−6/5, −4/5] | 0.534026 |
| [3/5, 4/5] | [−4/5, −2/5] | 0.438488 |
| [4/5, 1] | [−2/5, 0] | 0.319059 |

Every error is less than one, proving strict positive definiteness of all nine
corrected reduced matrix blocks throughout each interval. Every complete
polynomial inverse residual is below `5.593e-9`. Root existence and uniqueness,
basis inverses, the exact coefficient correction and equality exclusions also
passed. The first auxiliary cell **includes q=0**; no small interval near −2
has been discarded.

All five cells use the same **degree-12 Hermite profile**, **Taylor order 10**,
and unit certificate multiplier. The five compressed witnesses total
**483,848 bytes**. The positive source package uses 111 finite cells plus its
tail checks; no new large-exponent argument is needed here.

The publication run consists of five fresh standalone `verify_cell.py` workers,
then exact rational aggregation. Its status is
`PASS_FIVE_FRESH_CELLS_EXACT_UNION` in `verification/SUMMARY.json`.
The complete replay command below launches new workers and emits
`PASS_COMPLETE_NEGATIVE_RIESZ_REPLAY` only after every new computation succeeds.
It was not the launcher of the retained first run. Neither command treats a
stored report as a mathematical premise.

## The endpoint normalization

A direct continuation of the old matrices loses its margin as `s` approaches −2.
Instead define, for `0≤q≤1`,

    Ψ_q(t) = 2 ∫[-1,t] (t−u)(2−2u)^(−q−1) du.

For `q>0` this is

    Ψ_q(t) = [φ_(2q−2)(t) − φ_(2q−2)(−1) − 4^(−q)(t+1)]/q.

The new certificates prove that Ψ_q is minimized by an optimized square
antiprism for **the closed interval 0≤q≤1**. Its endpoint at q=0 is regular:

    Ψ_0(t) = (1−t) log((1−t)/2) + t + 1.

Because the antiprism has zero centroid, the exact energy difference is

    Ê_(2q−2)(Y) − Ê_(2q−2)(X(a))
      = (4^(−q)/2) |sum_i y_i|² + q [V_q(Y) − V_q(X(a))].

Here `V_q` is the unordered-pair sum of Ψ_q. Both terms on the right are
nonnegative once the auxiliary theorem is proved. For q>0, uniqueness follows
from the auxiliary certificate. **At s=−2 itself uniqueness does not follow and
is false: every zero-centroid configuration minimizes the original energy.**
See `proof.pdf` and `proof.tex` for the analytic argument, the collision case,
the regularized root, the entire-series tail bounds and the finite criterion.

## Recompute the complete extension

Run the commands below from `Certificates/Negative_s/` with ordinary Python
without `-O`. For the python-flint exact integer backend, install the pinned
requirements and use a new output directory.

```sh
python -m pip install -r requirements.txt
python -B cap.py replay --jobs 4 --output new-replay
```

The driver can be called from another working directory by giving its full path.
`--jobs` controls simultaneous cells. It fixes the proof parameters and numerical
library thread counts, checks the package manifest, starts fresh workers, verifies
all cell/source/witness bindings, and checks the exact rational union. An old or
incomplete output directory is rejected. A failed worker cannot yield a complete
success status.

For a byte-integrity check only:

```sh
python -B cap.py integrity
```

This does **not** prove a mathematical inequality.

One diagnostic cell (not a complete-range certificate):

```sh
python -B verify_cell.py q_1_10.json new-single-cell
```

## Recorded arithmetic backend

The verification performed here used **Python 3.13.5, NumPy 2.3.5, mpmath 1.3.0**,
and the included **GMP exact-integer matrix adapter**, because python-flint was
not installed in the execution environment. This adapter is **not python-flint**;
its identity is disclosed in every `ENVIRONMENT.json`.

It provides the small `fmpz_mat` interface used by the unchanged integer interval
code: integer construction, multiplication, addition and indexing. Its C++ source
uses GMP integer operations and no floating-point arithmetic. It passed 45
signed-integer regression test families, including empty products and integers
up to 800 bits, against Python integer products. These regression tests are
additional diagnostics, not a replacement for the uniform proof checks.

To use this optional backend on Linux with a C++17 compiler and GMP development
libraries installed:

```sh
python -m pip install -r requirements-gmp.txt
python -B cap.py replay --backend gmp --jobs 4 --output new-gmp-replay
```

The driver builds `portable_backend/gmp_matrix.so` from the included source if
needed. The run-specific shared-object hash is retained in the published input
bindings; the compiled object is not a portable publication input. The default
python-flint replay is the convenient route on Windows and requires no local C++
compilation. A replay using python-flint was not executed here; the recorded
successful replay used the disclosed GMP backend.

Run the optional diagnostic comparisons with:

```sh
python -B diagnostics.py --backend gmp --output diagnostic-results.json
```

The additional 80 high-precision comparisons of the potential and its derivatives
include both q endpoints. Their reference tolerance is never used by the proof
checker, which retains explicit outward error bounds.

## Source changes and proof scope

`PROVENANCE.json` binds the original ZIP and lists all inherited modules.
Thirteen kernel modules are byte-for-byte unchanged. The three modified modules
are:

- `taylor_models.py`: the regularized root and endpoint-safe auxiliary potential;
  the inherited Taylor arithmetic class is unchanged.
- `build_models.py`: disable the old positive-s target multiplier; these cells use
  the unit multiplier.
- `verify_interval.py`: update the result's scope text to the auxiliary parameter;
  the verification logic is unchanged.

`SOURCE_DIFF.patch` gives the exact changes. The new driver and five compact
witnesses are separate. `sources/positive_manuscript.tex` is an unmodified copy
of the supplied mathematical reduction. The original archive SHA-256 is recorded
in `PROVENANCE.json`. Its 641-file integrity check passed, but its 111 positive
finite cells and its tail computations were **not** rerun in this computation.

The result is a computer-assisted proof, **not a Lean formalization**. Numerical
roots, matrix inverses, eigenvectors and reconstructed witnesses are proposals.
Every acceptance bound uses the inherited integer interval arithmetic and explicit
series tails, with the exact-integer backend disclosed above. The proof still
relies on the mathematical reduction, correct indexing/control flow, Python,
the integer backend and the execution platform.
