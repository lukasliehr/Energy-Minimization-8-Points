import Thomson8.UniqueMinimum
import Coulomb8.UniqueMinimum
import Lean_Code.MainTheorem
import ThomsonCompact
import ThomsonNegative

/-!
# The verified cases

This entry point collects the global optimality theorems:

* `ThomsonCompact.Statement.all_s_global_optimality` (every real `s ≥ 0`, logarithmic at `s = 0`);
* `ThomsonNegative.Finalization.negative_s_global_optimality` (every real `-2 < s < 0`);
* `Thomson8.logarithmic_energy_N8_global_minimizer` (`s = 0`);
* `Coulomb8.coulomb_energy_N8_solution` (`s = 1`);
* `SquareAntiprismVerification.eventual_global_optimality` (sufficiently large `s`).

The first theorem contains the optimality statements of the last three; their developments
supply the exact minimal energies for `s = 0` and `s = 1`.
`LeanCode.Bridge` reconciles their coordinate and stationarity conventions.
`Showcase_WithProofs.lean` expresses them in the paper's common notation.
-/
