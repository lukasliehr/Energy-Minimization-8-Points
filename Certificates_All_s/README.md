# Optimal eight-point configurations for all nonnegative exponents

This directory contains certificates and checkers for the computer-assisted proof that the
optimized square antiprism uniquely minimizes Riesz energy among eight points
on the unit sphere, up to orthogonal transformations and relabeling, for every
real exponent `s > 0`. At `s = 0` the energy is logarithmic.

The finite certificates cover the closed interval `[0,124]`. An analytic tail
argument, with exact computational checks, covers every real `s >= 124`.
Each finite certificate is valid throughout its exponent interval.

The computations use exact integer enclosures. Numerical solvers supply
candidate matrices whose residuals are checked by exact arithmetic.
The full-range proof has not yet been formalized in Lean.

## Contents

- `cap.py`: the complete replay entry point.
- `finite/`: exact arithmetic, Taylor models, one finite checker and its cells.
- `certificates/finite/`: compact proposals, shared when cells use the same data.
- `tail/`: integer packing enumeration and exact geometric and scalar checks.
- `verification/`: complete verification records and input hashes.
- `docs/`: instructions for the certificate reader and arithmetic tests.

## Reproduce

Use Python 3.13. Some intervals require several gigabytes of memory each.
Set the number of concurrent intervals with `--jobs`.

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r requirements.txt
.venv/bin/python -B cap.py integrity
.venv/bin/python -B cap.py replay --jobs 1 --output /path/to/new-results
```

The output directory must not already exist. Use fewer workers on a machine
with less memory. The replay checks all source and witness hashes, recomputes
all 111 finite cells and all five tail components, and rejects missing or
failed obligations. `cap.py status` only displays the published result;
it does not perform a fresh proof computation. See [CAP.md](CAP.md).

The compact inputs specify candidate correction matrices. Their generated
entries are interpreted as exact dyadic rationals and checked independently.
See the [certificate reader tests](docs/FORMAT.md) and
[arithmetic tests](docs/EXACT_ARITHMETIC.md).
