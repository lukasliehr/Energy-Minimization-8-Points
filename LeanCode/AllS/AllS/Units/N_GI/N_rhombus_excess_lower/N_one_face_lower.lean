import AllS.Units.N_GI.N_rhombus_excess_lower.N_angle_interval
import AllS.Units.N_GI.N_rhombus_excess_lower.N_endpoint_value

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem rhombus_excess_lower_one_face_lower {Y : Fin 8 → Point} {c : ℝ}
    (D : ContactTilingData Y c) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) (f : Fin D.quadCount) :
    2 * D.triangleExcess ≤ D.excess f := by
  have hα := equilateral_angle_Ioo c hc
  have hgeom := rhombus_excess_lower_angle_interval D hY hc f 0
  have hend := rhombus_excess_lower_endpoint_value D hc
  rw [hgeom.2]
  exact Blueprint.TailEulerArithmetic.concave_endpoint_lower (by dsimp [ContactTilingData.alpha]; linarith [hα.1])
    (rhombusArea_strictConcave_equilateral_interval c D.alpha hc hα).concaveOn
    hend.1 hend.2 ⟨hgeom.1.1.le,hgeom.1.2.le⟩

#print axioms rhombus_excess_lower_one_face_lower

end Blueprint.Thomson.Tail.Implementation
