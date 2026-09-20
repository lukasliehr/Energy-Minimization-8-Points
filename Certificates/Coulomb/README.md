# Coulomb N=8 computer-assisted proof

This folder contains the simplified certificate and a standalone exact checker.
The certificate has 192 matrix coordinates in nine blocks of sizes 4, 5, 4, 3, 2, 1, 14, 8 and 3. A 99×99 exact linear correction has the uniform radius 2^-38.

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

The full Lean proof is in [`../../LeanCode/Coulomb`](../../LeanCode/Coulomb), and the public proved
statement is [`../../Showcase_WithProofs.lean`](../../Showcase_WithProofs.lean).
The proof uses only `propext`, `Classical.choice` and `Quot.sound`.
Python success is not used as a hypothesis or axiom in Lean.

The checker uses the same enlarged correction box as Lean: every coordinate,
including each unchanged coordinate, receives radius `2^-38`.

The standalone Lean certificate theorem is `Coulomb8.verified_CAP` in
[`VerifiedCAP.lean`](../../LeanCode/Coulomb/Coulomb8/VerifiedCAP.lean).
