import AllS.Units.N_GI.N_contact_taylor.N_scalar_bounds

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem chartRoot_scaled_loss (q : TangentCoordinates) (hq : ‖q‖ < 1) (i : Fin 8) :
    (1-chartRoot q i)*(1+√(1-‖q‖^2)) ≤ ‖tangentVector q i‖^2 := by
  obtain ⟨_,hs,hi⟩ := chartRoot_bounds q hq i
  have he := chartRoot_sq q hq i
  nlinarith [mul_nonneg (sub_nonneg.mpr hi) (sub_nonneg.mpr hs)]

theorem contact_cross_bound (q : TangentCoordinates) (hq : ‖q‖ < 1) (i j : Fin 8)
    (hc : inner ℝ (packingReference i) (packingReference j)=packingHeight) :
    |2*(1-chartRoot q i)*inner ℝ (packingReference i) (tangentVector q j)| ≤
      2*√(1-packingHeight^2)*‖tangentVector q i‖^2*‖tangentVector q j‖/(1+√(1-‖q‖^2)) := by
  have hi := (chartRoot_bounds q hq i).2.2
  have hs := (chartRoot_bounds q hq i).1
  have hc0 := Real.sqrt_nonneg (1-packingHeight^2)
  have hinner := contact_inner_bound q i j hc
  have hscaled := chartRoot_scaled_loss q hq i
  have hm := mul_le_mul_of_nonneg_right hscaled
    (show 0 ≤ 2*√(1-packingHeight^2)*‖tangentVector q j‖ by positivity)
  rw [abs_mul,abs_of_nonneg (show 0 ≤ 2*(1-chartRoot q i) by positivity)]
  calc
    _ ≤ 2*(1-chartRoot q i)*(√(1-packingHeight^2)*‖tangentVector q j‖) := by
      gcongr
    _ ≤ _ := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith

theorem chartRoot_pair_difference_sq (q : TangentCoordinates) (hq : ‖q‖ < 1)
    (i j : Fin 8) (hij : i ≠ j) :
    (chartRoot q i-chartRoot q j)^2 ≤
      ‖q‖^2*(‖tangentVector q i‖^2+‖tangentVector q j‖^2)/(4*(1-‖q‖^2)) := by
  obtain ⟨hs0,hi,_⟩ := chartRoot_bounds q hq i
  obtain ⟨_,hj,_⟩ := chartRoot_bounds q hq j
  have hq0 := norm_nonneg q
  have hden : 0 < 1-‖q‖^2 := by nlinarith
  have hs2 := Real.sq_sqrt hden.le
  have hsq : 4*(1-‖q‖^2) ≤ (chartRoot q i+chartRoot q j)^2 := by
    nlinarith
  have he : (chartRoot q i-chartRoot q j)^2*(chartRoot q i+chartRoot q j)^2=
      (‖tangentVector q i‖^2-‖tangentVector q j‖^2)^2 := by
    have hh : (chartRoot q i-chartRoot q j)*(chartRoot q i+chartRoot q j)=
        -(‖tangentVector q i‖^2-‖tangentVector q j‖^2) := by
      nlinarith [chartRoot_sq q hq i,chartRoot_sq q hq j]
    nlinarith [sq_nonneg ((chartRoot q i-chartRoot q j)*(chartRoot q i+chartRoot q j)+
      (‖tangentVector q i‖^2-‖tangentVector q j‖^2))]
  have hu := sq_nonneg ‖tangentVector q i‖
  have hv := sq_nonneg ‖tangentVector q j‖
  have hp := tangentVector_pair_norm_sq q i j hij
  have hm := mul_le_mul_of_nonneg_right hp (add_nonneg hu hv)
  have hd : (‖tangentVector q i‖^2-‖tangentVector q j‖^2)^2 ≤
      ‖q‖^2*(‖tangentVector q i‖^2+‖tangentVector q j‖^2) := by
    nlinarith [mul_nonneg hu hv]
  have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg (chartRoot q i-chartRoot q j))
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

theorem chartRoot_product_loss (q : TangentCoordinates) (hq : ‖q‖ < 1) (i j : Fin 8) :
    0 ≤ 1-chartRoot q i*chartRoot q j ∧
    1-chartRoot q i*chartRoot q j ≤
      (‖tangentVector q i‖^2+‖tangentVector q j‖^2)/(1+√(1-‖q‖^2)) := by
  obtain ⟨hs0,hi,hi1⟩ := chartRoot_bounds q hq i
  obtain ⟨_,hj,hj1⟩ := chartRoot_bounds q hq j
  have hprod : chartRoot q i*chartRoot q j ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hi1) (show 0 ≤ chartRoot q j by linarith)]
  refine ⟨sub_nonneg.mpr hprod,?_⟩
  apply (le_div_iff₀ (by positivity)).mpr
  have ha := chartRoot_scaled_loss q hq i
  have hb := chartRoot_scaled_loss q hq j
  have hmul : 1-chartRoot q i*chartRoot q j ≤ (1-chartRoot q i)+(1-chartRoot q j) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hi1) (sub_nonneg.mpr hj1)]
  have hh := mul_le_mul_of_nonneg_right hmul (show 0 ≤ 1+√(1-‖q‖^2) by positivity)
  linarith

#print axioms contact_cross_bound
#print axioms chartRoot_pair_difference_sq
#print axioms chartRoot_product_loss
end Blueprint.Thomson.Tail.Implementation
