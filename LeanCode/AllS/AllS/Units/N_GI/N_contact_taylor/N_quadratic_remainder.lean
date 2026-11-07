import AllS.Units.N_GI.N_contact_taylor.N_cubic_remainder

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem contact_delta_remainder_formula (q : TangentCoordinates) (hq : ‖q‖ ≤ 3/10)
    (i j : Fin 8) (hc : inner ℝ (packingReference i) (packingReference j)=packingHeight) :
    contactDelta q i j-contactLinear q i j=
      2*packingHeight*(1-chartRoot q i*chartRoot q j)-2*inner ℝ (tangentVector q i) (tangentVector q j)+
      2*(1-chartRoot q i)*inner ℝ (packingReference i) (tangentVector q j)+
      2*(1-chartRoot q j)*inner ℝ (packingReference j) (tangentVector q i) := by
  have hq1 : ‖q‖ < 1 := by linarith
  have he := contact_taylor_exact_expansion q hq i j hc
  dsimp [contactQuadratic,contactRemainder] at he
  linear_combination he+packingHeight*(chartRoot_sq q hq1 i)+packingHeight*(chartRoot_sq q hq1 j)

theorem contact_quadratic_gamma_bound (q : TangentCoordinates) (hq : ‖q‖ ≤ 3/10)
    (i j : Fin 8) (hc : inner ℝ (packingReference i) (packingReference j)=packingHeight) :
    |contactDelta q i j-contactLinear q i j| ≤
      contactGamma ‖q‖*(‖tangentVector q i‖^2+‖tangentVector q j‖^2) := by
  have hq1 : ‖q‖ < 1 := by linarith
  have ha : 0 ≤ packingHeight := by linarith [contact_packing_bounds.1]
  have hroot := chartRoot_product_loss q hq1 i j
  have hcross := contact_cross_sum_bound q hq1 i j hc
  have hdot := abs_real_inner_le_norm (tangentVector q i) (tangentVector q j)
  have hdot2 : |2*inner ℝ (tangentVector q i) (tangentVector q j)| ≤
      ‖tangentVector q i‖^2+‖tangentVector q j‖^2 := by
    rw [abs_mul,abs_of_nonneg (show (0:ℝ) ≤ 2 by norm_num)]
    nlinarith [sq_nonneg (‖tangentVector q i‖-‖tangentVector q j‖)]
  have hr := mul_le_mul_of_nonneg_left hroot.2 (show 0 ≤ 2*packingHeight by positivity)
  have ht : |contactDelta q i j-contactLinear q i j| ≤
      2*packingHeight*(1-chartRoot q i*chartRoot q j)+
      |2*inner ℝ (tangentVector q i) (tangentVector q j)|+
      |2*(1-chartRoot q i)*inner ℝ (packingReference i) (tangentVector q j)|+
      |2*(1-chartRoot q j)*inner ℝ (packingReference j) (tangentVector q i)| := by
    rw [contact_delta_remainder_formula q hq i j hc]
    have hab := abs_add_le (2*packingHeight*(1-chartRoot q i*chartRoot q j))
      (-(2*inner ℝ (tangentVector q i) (tangentVector q j)))
    simp only [abs_neg,← sub_eq_add_neg] at hab
    rw [abs_of_nonneg (mul_nonneg (by positivity) hroot.1 : 0 ≤ 2*packingHeight*(1-chartRoot q i*chartRoot q j))] at hab
    have habc := abs_add_le
      (2*packingHeight*(1-chartRoot q i*chartRoot q j)-2*inner ℝ (tangentVector q i) (tangentVector q j))
      (2*(1-chartRoot q i)*inner ℝ (packingReference i) (tangentVector q j))
    have habcd := abs_add_le
      (2*packingHeight*(1-chartRoot q i*chartRoot q j)-2*inner ℝ (tangentVector q i) (tangentVector q j)+
        2*(1-chartRoot q i)*inner ℝ (packingReference i) (tangentVector q j))
      (2*(1-chartRoot q j)*inner ℝ (packingReference j) (tangentVector q i))
    linarith
  calc
    _ ≤ 2*packingHeight*((‖tangentVector q i‖^2+‖tangentVector q j‖^2)/(1+√(1-‖q‖^2)))+
        (‖tangentVector q i‖^2+‖tangentVector q j‖^2)+
        √(2*(1-packingHeight^2))*‖q‖/(1+√(1-‖q‖^2))*
          (‖tangentVector q i‖^2+‖tangentVector q j‖^2) := by linarith
    _ = _ := by dsimp [contactGamma]; ring

theorem contact_taylor_quadratic_remainder (q : TangentCoordinates) (hq : ‖q‖ ≤ 3/10)
    (i j : Fin 8) (hc : inner ℝ (packingReference i) (packingReference j)=packingHeight) :
    |contactDelta q i j-contactLinear q i j| ≤
      (3/2)*(‖tangentVector q i‖^2+‖tangentVector q j‖^2) ∧
    (3/2)*(‖tangentVector q i‖^2+‖tangentVector q j‖^2) ≤ (3/2)*‖q‖^2 := by
  have he := contact_quadratic_gamma_bound q hq i j hc
  have hgamma := (contact_scalar_bounds ‖q‖ (norm_nonneg _) hq).2
  have hn : 0 ≤ ‖tangentVector q i‖^2+‖tangentVector q j‖^2 := by positivity
  have hp := tangentVector_pair_norm_sq q i j (contact_distinct i j hc)
  constructor
  · exact he.trans (mul_le_mul_of_nonneg_right hgamma.le hn)
  · linarith

#check contact_taylor_quadratic_remainder
#print axioms contact_taylor_quadratic_remainder
end Blueprint.Thomson.Tail.Implementation
