import Thomson8.UniqueMinimum
import Coulomb8.UniqueMinimum
import Lean_Code.MainTheorem

/-!
# The three verified cases

This entry point collects the original global optimality theorems:

* `Thomson8.logarithmic_energy_N8_global_minimizer` (`s = 0`);
* `Coulomb8.coulomb_energy_N8_solution` (`s = 1`);
* `SquareAntiprismVerification.eventual_global_optimality` (sufficiently large `s`).

`LeanCode.Bridge` reconciles their coordinate and stationarity conventions.
`Showcase_WithProofs.lean` expresses them in the paper's common notation.
-/
