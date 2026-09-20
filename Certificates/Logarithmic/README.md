# Logarithmic N=8 computer-assisted proof

This folder contains the simplified certificate and a standalone exact checker.
The certificate has 299 matrix coordinates in seven blocks of sizes 6, 5, 4, 2, 1, 18 and 12. Its entries are explicit affine expressions in four logarithms; no matrix correction is needed.

## Recheck

From this folder, with Python 3.9 or newer:

```sh
python3 verify.py
```

Only the Python standard library is required. The checker reconstructs and
checks the certificate using exact rational arithmetic and integer interval
bounds. A successful run writes `verification.json`. No search or optimizer
is needed.

## Contents

- `certificate.json`: the exact witness used in the Lean verification.
- `verify.py` and the supporting Python modules: the independent CAP checker.
- `lean_data/`: supplementary exact data exported during formalization.

The full Lean proof is in [`../../LeanCode/Logarithmic`](../../LeanCode/Logarithmic), and the public proved
statement is [`../../Showcase_WithProofs.lean`](../../Showcase_WithProofs.lean).
The proof uses only `propext`, `Classical.choice` and `Quot.sound`.
Python success is not used as a hypothesis or axiom in Lean.

The exact polynomial identity is assembled in
[`RealIdentity.lean`](../../LeanCode/Logarithmic/Thomson8/RealIdentity.lean), and the
certificate positivity is proved in
[`Positivity.lean`](../../LeanCode/Logarithmic/Thomson8/Positivity.lean).
