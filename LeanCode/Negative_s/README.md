# Global optimality for every exponent `-2 < s < 0`

This directory contains the Lean proof of global optimality of the square antiprism for every real
$-2\lt s\lt0$, for the energy divided by $s$. The final theorem is
`ThomsonNegative.Finalization.negative_s_global_optimality` in
[ThomsonNegative/Finalization/Verified.lean](ThomsonNegative/Finalization/Verified.lean). It is stated with
verbatim copies of the definitions of [Showcase.lean](../../Showcase.lean), and
[Showcase_WithProofs.lean](../../Showcase_WithProofs.lean) combines it with [LeanCode/AllS](../AllS) into the
theorem for every $s\gt-2$.

The proof subtracts an exactly summable centroid term from the energy and covers $q=(s+2)/2\in[0,1]$ by
five cells. In each cell, Bernstein square factors give a positive floor and four weighted correction bounds
are checked against it; polynomial identities prove the exact inverse of the coefficient map. The
computer-assisted part is checked by Boolean checkers with proofs of soundness, evaluated in the Lean kernel
by `decide +kernel` on packed natural-number data. No `native_decide` is used. At $s=-2$ the minimizers are
exactly the configurations with centroid zero (`ThomsonNegative.energy_minus_two_minimum`), so uniqueness
fails there.

| Path | Contents |
| --- | --- |
| [ThomsonNegative/Finalization](ThomsonNegative/Finalization) | The five checked cells, the minimizer theorem and the statement of the showcase. |
| [ThomsonNegative/Geometry](ThomsonNegative/Geometry) | Hermite interpolation, energy comparison, equality, moments and congruence. |
| [ThomsonNegative/Analytic](ThomsonNegative/Analytic) | Root bounds and margin, Rolle and Lipschitz transfer, and the scalar reduction. |
| [ThomsonNegative/Compact](ThomsonNegative/Compact) | Packed arithmetic, scalar and root bounds, and the five scalar cells. |
| [ThomsonNegative/Structure](ThomsonNegative/Structure) | The exact coefficient map, compatibility and structural repair. |
| [ThomsonNegative/Certificate](ThomsonNegative/Certificate) | Matrix enclosures, exact table bridges and correction bounds. |
| [ThomsonNegative/Reduction](ThomsonNegative/Reduction), [ThomsonNegative/CertificateReduction](ThomsonNegative/CertificateReduction) | Correction floor, denominators, equality and contact counts. |
| Files in [ThomsonNegative](ThomsonNegative) | Definitions, the energy decomposition, the stationary root and the series of the auxiliary potential. |

The development was written for Lean 4.32.0. For this repository, a few proof steps in seven files were
adapted to Lean 4.33.0 and the pinned Mathlib:
[GramSound.lean](ThomsonNegative/Certificate/GramSound.lean),
[RawMix.lean](ThomsonNegative/Certificate/Bridges/RawMix.lean),
[ProgramBridge.lean](ThomsonNegative/Certificate/Bridges/ProgramBridge.lean),
[Functionals.lean](ThomsonNegative/Structure/Functionals.lean),
[HighImage.lean](ThomsonNegative/Structure/Concrete/HighImage.lean),
[SourceOperator.lean](ThomsonNegative/Structure/Concrete/SourceOperator.lean) and
[SourceRepair.lean](ThomsonNegative/Finalization/SourceRepair.lean). No statement was changed. The final
theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.
