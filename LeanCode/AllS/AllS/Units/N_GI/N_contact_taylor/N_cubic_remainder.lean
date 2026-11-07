import AllS.Units.N_GI.N_contact_taylor.N_remainder_helpers

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem contact_cross_sum_bound (q : TangentCoordinates) (hq : ‖q‖ < 1)
    (i j : Fin 8) (hc : inner ℝ (packingReference i) (packingReference j)=packingHeight) :
    |2*(1-chartRoot q i)*inner ℝ (packingReference i) (tangentVector q j)|+
    |2*(1-chartRoot q j)*inner ℝ (packingReference j) (tangentVector q i)| ≤
      √(2*(1-packingHeight^2))*‖q‖/(1+√(1-‖q‖^2))*
        (‖tangentVector q i‖^2+‖tangentVector q j‖^2) := by
  have hji : inner ℝ (packingReference j) (packingReference i)=packingHeight := by
    rwa [real_inner_comm]
  have h1 := contact_cross_bound q hq i j hc
  have h2 := contact_cross_bound q hq j i hji
  have hp := pair_cubic_bound _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
    (tangentVector_pair_norm_sq q i j (contact_distinct i j hc))
  have hm := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ 2*√(1-packingHeight^2)/(1+√(1-‖q‖^2)) by positivity)
  have hs2 : (√(2:ℝ))^2=2 := Real.sq_sqrt (by norm_num)
  have hspos : 0 < √(2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have he : 2*√(1-packingHeight^2)/√2=√(2*(1-packingHeight^2)) := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    apply (div_eq_iff (ne_of_gt hspos)).mpr
    linear_combination -√(1-packingHeight^2)*hs2
  calc
    _ ≤ 2*√(1-packingHeight^2)*‖tangentVector q i‖^2*‖tangentVector q j‖/(1+√(1-‖q‖^2))+
        2*√(1-packingHeight^2)*‖tangentVector q j‖^2*‖tangentVector q i‖/(1+√(1-‖q‖^2)) := add_le_add h1 h2
    _ = (2*√(1-packingHeight^2)/(1+√(1-‖q‖^2)))*
        (‖tangentVector q i‖^2*‖tangentVector q j‖+‖tangentVector q j‖^2*‖tangentVector q i‖) := by ring
    _ ≤ _ := hm
    _ = (2*√(1-packingHeight^2)/√2)*‖q‖/(1+√(1-‖q‖^2))*
        (‖tangentVector q i‖^2+‖tangentVector q j‖^2) := by ring
    _ = _ := by rw [he]

theorem contact_taylor_cubic_remainder (q : TangentCoordinates) (hq : ‖q‖ ≤ 3/10)
    (i j : Fin 8) (hc : inner ℝ (packingReference i) (packingReference j)=packingHeight) :
    |contactRemainder q i j| ≤ contactH ‖q‖*(‖tangentVector q i‖^2+‖tangentVector q j‖^2) ∧
    contactH ‖q‖ < 11/50 := by
  have hq1 : ‖q‖ < 1 := by linarith
  have ha : 0 ≤ packingHeight := by linarith [contact_packing_bounds.1]
  have hsq := mul_le_mul_of_nonneg_left
    (chartRoot_pair_difference_sq q hq1 i j (contact_distinct i j hc)) ha
  have hcross := contact_cross_sum_bound q hq1 i j hc
  have htri : |contactRemainder q i j| ≤
      packingHeight*(chartRoot q i-chartRoot q j)^2+
      |2*(1-chartRoot q i)*inner ℝ (packingReference i) (tangentVector q j)|+
      |2*(1-chartRoot q j)*inner ℝ (packingReference j) (tangentVector q i)| := by
    unfold contactRemainder
    calc
      _ ≤ |packingHeight*(chartRoot q i-chartRoot q j)^2+
            2*(1-chartRoot q i)*inner ℝ (packingReference i) (tangentVector q j)|+
          |2*(1-chartRoot q j)*inner ℝ (packingReference j) (tangentVector q i)| := abs_add_le _ _
      _ ≤ _ := by
        have h := abs_add_le (packingHeight*(chartRoot q i-chartRoot q j)^2)
          (2*(1-chartRoot q i)*inner ℝ (packingReference i) (tangentVector q j))
        rw [abs_of_nonneg (by positivity : 0 ≤ packingHeight*(chartRoot q i-chartRoot q j)^2)] at h
        linarith
  refine ⟨?_,(contact_scalar_bounds ‖q‖ (norm_nonneg _) hq).1⟩
  calc
    _ ≤ packingHeight*(‖q‖^2*(‖tangentVector q i‖^2+‖tangentVector q j‖^2)/(4*(1-‖q‖^2)))+
        √(2*(1-packingHeight^2))*‖q‖/(1+√(1-‖q‖^2))*
          (‖tangentVector q i‖^2+‖tangentVector q j‖^2) := by linarith
    _ = _ := by dsimp [contactH]; ring

#check contact_taylor_cubic_remainder
#print axioms contact_taylor_cubic_remainder
end Blueprint.Thomson.Tail.Implementation
