import AllS.Units.N_G.N_setup
import Lean_Code.ContactTilingData
import Blueprint.TailEulerArithmetic

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem rhombus_excess_lower_angle_interval {Y : Fin 8 → Point} {c : ℝ}
    (D : ContactTilingData Y c) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (f : Fin D.quadCount) (j : Fin 4) :
    D.angle f j ∈ Set.Ioo D.alpha (2 * D.alpha) ∧
      D.excess f = rhombusArea (1/c) (D.angle f j) :=
  D.corner_geometry hY hc f j

#print axioms rhombus_excess_lower_angle_interval

end Blueprint.Thomson.Tail.Implementation
