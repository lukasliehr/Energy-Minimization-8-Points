import AllS.Units.N_GI.N_pair_hessian.N_pair_eight_thirds

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem pair_hessian_assemble (p : ℝ) (hp : (97:ℝ)/2≤p) (q ξ : TangentCoordinates)
    (hq : ‖q‖≤contraction/p) (i j : Fin 8) (hij : i≠j) :
    pairSecond q ξ i j≤(8:ℝ)/3*(‖tangentVector ξ i‖^2+‖tangentVector ξ j‖^2) := by
  have hq1 : ‖q‖<1 := by have h := tail_small_radius p hp q hq;linarith
  exact (pair_hessian_pair_upper_formula q ξ hq1 i j hij).trans
    (mul_le_mul_of_nonneg_right (pair_hessian_pair_eight_thirds p hp q hq).le (by positivity))

#print axioms pair_hessian_assemble
end Blueprint.Thomson.Tail.Implementation
