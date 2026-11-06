import AllS.Units.N_GI.N_pair_hessian.N_pair_second
import AllS.Units.N_GI.N_tail_rational.N_analytic_bounds

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def pairHessianBound (r : ℝ) : ℝ :=
  2/(chartMinRoot r)^2+2*(packingHeight+chartStretch r*r)/(chartMinRoot r)^3

theorem packingReference_inner_upper (i j : Fin 8) (hij : i≠j) :
    inner ℝ (packingReference i) (packingReference j)≤packingHeight := by
  rw [packingReference_inner_cyclic,if_neg hij]
  split_ifs <;> nlinarith [tail_geometric_constants.1,tail_geometric_constants.2.1]

theorem reference_chart_inner_upper (q : TangentCoordinates) (hq : ‖q‖<1) (i j : Fin 8) (hij : i≠j) :
    inner ℝ (packingReference i) (orthographicChart q j)≤packingHeight+chartStretch ‖q‖*‖q‖ := by
  have h := (le_abs_self (inner ℝ (packingReference i) (orthographicChart q j-packingReference j))).trans
    (abs_real_inner_le_norm (packingReference i) (orthographicChart q j-packingReference j))
  rw [packingReference_norm,one_mul,inner_sub_right] at h
  have hd := (chart_deviation_stretch q hq j).trans
    (mul_le_mul_of_nonneg_left (tangentVector_norm_le q j) (chartStretch_nonneg _))
  have hp := packingReference_inner_upper i j hij
  linarith

theorem pair_hessian_pair_upper_formula (q ξ : TangentCoordinates) (hq : ‖q‖<1)
    (i j : Fin 8) (hij : i≠j) :
    pairSecond q ξ i j≤pairHessianBound ‖q‖*(‖tangentVector ξ i‖^2+‖tangentVector ξ j‖^2) := by
  have hs : 0<chartMinRoot ‖q‖ := (chartRoot_bounds q hq i).1
  have hc := chartStretch_nonneg ‖q‖
  have ha : 0≤packingHeight := by linarith [tail_geometric_constants.1]
  have hb : 0≤packingHeight+chartStretch ‖q‖*‖q‖ := by positivity
  have hi : chartSecondCoefficient q ξ i*inner ℝ (packingReference i) (orthographicChart q j)≤
      (‖tangentVector ξ i‖^2/(chartMinRoot ‖q‖)^3)*(packingHeight+chartStretch ‖q‖*‖q‖) := by
    exact (mul_le_mul_of_nonneg_left (reference_chart_inner_upper q hq i j hij)
      (chartSecondCoefficient_nonneg q ξ hq i)).trans
      (mul_le_mul_of_nonneg_right (chartSecondCoefficient_upper q ξ hq i) hb)
  have hj : chartSecondCoefficient q ξ j*inner ℝ (packingReference j) (orthographicChart q i)≤
      (‖tangentVector ξ j‖^2/(chartMinRoot ‖q‖)^3)*(packingHeight+chartStretch ‖q‖*‖q‖) := by
    exact (mul_le_mul_of_nonneg_left (reference_chart_inner_upper q hq j i hij.symm)
      (chartSecondCoefficient_nonneg q ξ hq j)).trans
      (mul_le_mul_of_nonneg_right (chartSecondCoefficient_upper q ξ hq j) hb)
  have hcross : -inner ℝ (chartDerivative q i ξ) (chartDerivative q j ξ)≤
      ‖tangentVector ξ i‖*‖tangentVector ξ j‖/(chartMinRoot ‖q‖)^2 := by
    have h := (neg_le_abs (inner ℝ (chartDerivative q i ξ) (chartDerivative q j ξ))).trans
      ((abs_real_inner_le_norm _ _).trans (mul_le_mul (chartDerivative_norm q ξ hq i)
        (chartDerivative_norm q ξ hq j) (norm_nonneg _) (by positivity)))
    convert! h using 1 <;> ring
  have hpair : 4*(‖tangentVector ξ i‖*‖tangentVector ξ j‖/(chartMinRoot ‖q‖)^2)≤
      (2/(chartMinRoot ‖q‖)^2)*(‖tangentVector ξ i‖^2+‖tangentVector ξ j‖^2) := by
    have h := mul_le_mul_of_nonneg_left
      (show 2*‖tangentVector ξ i‖*‖tangentVector ξ j‖≤‖tangentVector ξ i‖^2+‖tangentVector ξ j‖^2 by
        nlinarith [sq_nonneg (‖tangentVector ξ i‖-‖tangentVector ξ j‖)])
      (show 0≤2/(chartMinRoot ‖q‖)^2 by positivity)
    convert! h using 1 <;> ring
  rw [pairSecond_identity]
  dsimp [pairHessianBound]
  simp only [div_eq_mul_inv] at hi hj hcross hpair ⊢
  nlinarith

#print axioms pair_hessian_pair_upper_formula
end Blueprint.Thomson.Tail.Implementation
