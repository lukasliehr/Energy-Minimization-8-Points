import AllS.Units.N_GI.N_slice_point_bound.N_evaluation_norm

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem slice_point_bound_assemble (q : TangentCoordinates) (hq : q∈rotationSlice) (i : Fin 8) :
    ‖tangentVector q i‖^2 ≤ (1-Real.sqrt 2/8)*(∑ j : Fin 8, ‖tangentVector q j‖^2) := by
  rw [tangentVector_sum_norm_sq]
  exact slice_point_bound_evaluation_norm q hq i

#print axioms slice_point_bound_assemble
end Blueprint.Thomson.Tail.Implementation
