import AllS.Units.N_GI.N_pair_hessian.N_chart_second
import AllS.Units.N_GI.N_derivative_stability.N_metric_bounds

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem tangent_inner_sq (q ξ : TangentCoordinates) (i : Fin 8) :
    (inner ℝ (tangentVector q i) (tangentVector ξ i))^2≤‖tangentVector q i‖^2*‖tangentVector ξ i‖^2 := by
  have h := mul_self_le_mul_self (abs_nonneg _) (abs_real_inner_le_norm (tangentVector q i) (tangentVector ξ i))
  nlinarith [sq_abs (inner ℝ (tangentVector q i) (tangentVector ξ i))]

theorem chartDerivative_norm_sq (q ξ : TangentCoordinates) (i : Fin 8) :
    ‖chartDerivative q i ξ‖^2=‖tangentVector ξ i‖^2+
      (inner ℝ (tangentVector q i) (tangentVector ξ i)/chartRoot q i)^2 := by
  rw [chartDerivative_apply,norm_sub_sq_real,norm_smul,packingReference_norm,
    real_inner_smul_right,tangentVector_orthogonal,Real.norm_eq_abs,mul_one,sq_abs]
  ring

theorem chartDerivative_norm (q ξ : TangentCoordinates) (hq : ‖q‖<1) (i : Fin 8) :
    ‖chartDerivative q i ξ‖≤‖tangentVector ξ i‖/chartMinRoot ‖q‖ := by
  obtain ⟨hs,hsi,_⟩ := chartRoot_bounds q hq i
  have hi : 0<chartRoot q i := hs.trans_le hsi
  have hsq := chartRoot_sq q hq i
  have hc := tangent_inner_sq q ξ i
  have hb : ‖chartDerivative q i ξ‖^2≤(‖tangentVector ξ i‖/chartRoot q i)^2 := by
    rw [chartDerivative_norm_sq,div_pow,div_pow]
    apply (le_div_iff₀ (sq_pos_of_pos hi)).mpr
    field_simp [hi.ne']
    nlinarith [sq_nonneg ‖tangentVector ξ i‖]
  have hl : ‖chartDerivative q i ξ‖≤‖tangentVector ξ i‖/chartRoot q i := by
    have hp : 0≤‖tangentVector ξ i‖/chartRoot q i := div_nonneg (norm_nonneg _) hi.le
    nlinarith [norm_nonneg (chartDerivative q i ξ)]
  exact hl.trans (div_le_div_of_nonneg_left (norm_nonneg _) hs hsi)

theorem chartSecondCoefficient_nonneg (q ξ : TangentCoordinates) (hq : ‖q‖<1) (i : Fin 8) :
    0≤chartSecondCoefficient q ξ i := by
  have hi := lt_of_lt_of_le (chartRoot_bounds q hq i).1 (chartRoot_bounds q hq i).2.1
  dsimp [chartSecondCoefficient]
  positivity

theorem chartSecondCoefficient_upper (q ξ : TangentCoordinates) (hq : ‖q‖<1) (i : Fin 8) :
    chartSecondCoefficient q ξ i≤‖tangentVector ξ i‖^2/(chartMinRoot ‖q‖)^3 := by
  obtain ⟨hs,hsi,_⟩ := chartRoot_bounds q hq i
  have hi : 0<chartRoot q i := hs.trans_le hsi
  have hsq := chartRoot_sq q hq i
  have hc := tangent_inner_sq q ξ i
  have hb : chartSecondCoefficient q ξ i≤‖tangentVector ξ i‖^2/(chartRoot q i)^3 := by
    dsimp [chartSecondCoefficient]
    apply (le_div_iff₀ (pow_pos hi 3)).mpr
    field_simp [hi.ne']
    nlinarith [sq_nonneg ‖tangentVector ξ i‖]
  apply hb.trans
  apply div_le_div_of_nonneg_left (sq_nonneg _) (pow_pos hs 3)
  exact pow_le_pow_left₀ hs.le hsi 3

#print axioms chartDerivative_norm
#print axioms chartSecondCoefficient_upper
end Blueprint.Thomson.Tail.Implementation
