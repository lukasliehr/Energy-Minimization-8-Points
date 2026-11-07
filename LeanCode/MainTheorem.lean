import Lean_Code.MainTheorem
import ThomsonCompact
import ThomsonNegative

/-!
# The verified cases

This entry point collects the global optimality theorems:

* `ThomsonCompact.Statement.all_s_global_optimality` (every real `s ≥ 0`, logarithmic at `s = 0`);
* `ThomsonNegative.Finalization.negative_s_global_optimality` (every real `-2 < s < 0`);
* `SquareAntiprismVerification.eventual_global_optimality` (sufficiently large `s`).

The first theorem contains the optimality statement of the last one.
`LeanCode.Bridge` relates the coordinates of the last development to those of the paper.
`Showcase_WithProofs.lean` expresses them in the paper's common notation.
-/
