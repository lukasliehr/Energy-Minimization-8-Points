import AllS.Units.N_GI.N_signed_mean.N_quartic_error

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem signed_mean_coefficient (r : ℝ) (hr : 0 ≤ r) (hrho : r ≤ 3/10) :
    (829:ℝ)/200+(11:ℝ)/10*r^2+(4*r+231/100)*r^2/(1+√(1-r^2))^2 ≤ 14063/3250 := by
  have hr2 : r^2 ≤ (9:ℝ)/100 := by nlinarith
  have hs : (19:ℝ)/20 ≤ √(1-r^2) := by
    apply (Real.le_sqrt (by norm_num : (0:ℝ) ≤ 19/20) (by nlinarith : 0 ≤ 1-r^2)).mpr
    nlinarith
  have hd : (39:ℝ)/20 ≤ 1+√(1-r^2) := by linarith
  have hfrac : (4*r+231/100)*r^2/(1+√(1-r^2))^2 ≤
      ((351:ℝ)/100)*(9/100)/((39:ℝ)/20)^2 := by
    gcongr <;> nlinarith
  nlinarith

theorem signed_mean_coefficient_strict : (14063:ℝ)/3250 < contactTotalWeight/5 := by
  have hs : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hlo : (1414:ℝ)/1000 < √2 := by nlinarith [Real.sqrt_nonneg (2:ℝ)]
  unfold contactTotalWeight
  linarith

theorem signed_mean_bound_of_cubic (hC : MeanCubicAbsorption) (q : TangentCoordinates) (hq : ‖q‖ ≤ 3/10) :
    contactMeanDelta q ≤ ‖q‖^2/5 ∧ (q≠0 → contactMeanDelta q < ‖q‖^2/5) := by
  have hc := signed_mean_after_cubic hC q hq
  have hcoef := signed_mean_coefficient ‖q‖ (norm_nonneg q) hq
  have hsmall := signed_mean_coefficient_strict
  have hW : 0 < contactTotalWeight := by unfold contactTotalWeight; positivity
  have hu : contactWeightedDelta q ≤ (14063:ℝ)/3250*‖q‖^2 :=
    hc.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
  unfold contactMeanDelta
  constructor
  · apply (div_le_iff₀ hW).mpr
    have hh := mul_le_mul_of_nonneg_right hsmall.le (sq_nonneg ‖q‖)
    nlinarith
  · intro hq0
    apply (div_lt_iff₀ hW).mpr
    have hh := mul_lt_mul_of_pos_right hsmall (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hq0))
    nlinarith

#print axioms signed_mean_coefficient
#print axioms signed_mean_bound_of_cubic
end Blueprint.Thomson.Tail.Implementation
