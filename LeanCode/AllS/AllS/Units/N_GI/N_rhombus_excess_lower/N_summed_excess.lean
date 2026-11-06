import AllS.Units.N_GI.N_rhombus_excess_lower.N_one_face_lower

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem rhombus_excess_lower_summed_excess {Y : Fin 8 → Point} {c : ℝ}
    (D : ContactTilingData Y c) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    2 * (D.quadCount : ℝ) * D.triangleExcess ≤ D.quadTotal := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun f _ => rhombus_excess_lower_one_face_lower D hY hc f)
  simpa [ContactTilingData.quadTotal, mul_assoc, mul_left_comm, mul_comm] using h

#print axioms rhombus_excess_lower_summed_excess

end Blueprint.Thomson.Tail.Implementation
