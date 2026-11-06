import AllS.Units.N_G.N_setup
import Lean_Code.ContactTilingData
import Blueprint.TailEulerArithmetic

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem rhombus_excess_lower_endpoint_value {Y : Fin 8 → Point} {c : ℝ}
    (D : ContactTilingData Y c) (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    rhombusArea (1/c) D.alpha = 2 * (3 * D.alpha - Real.pi) ∧
      rhombusArea (1/c) (2 * D.alpha) = 2 * (3 * D.alpha - Real.pi) := by
  have hd : 0 < 1+c := by linarith [hc.1]
  have hr : c/(1+c) ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · exact (by norm_num : (-1:ℝ) ≤ 0).trans (div_nonneg hc.1.le hd.le)
    · exact (div_le_one hd).mpr (by linarith)
  apply rhombusArea_endpoints c D.alpha hc.1 (equilateral_angle_Ioo c hc)
  exact Real.cos_arccos hr.1 hr.2

#print axioms rhombus_excess_lower_endpoint_value

end Blueprint.Thomson.Tail.Implementation
