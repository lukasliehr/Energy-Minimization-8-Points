import AllS.Units.N_GI.N_full_hessian.N_exact_hessian

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem pairDerivative_symm (q : TangentCoordinates) (i j : Fin 8) :
    pairDerivative q i j=pairDerivative q j i := by
  ext ξ
  simp only [pairDerivative,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply,innerSL_apply_apply,inner_sub_left,inner_sub_right,
    nsmul_eq_mul,Nat.cast_ofNat]
  ring

theorem contactPair_derivative (q ξ : TangentCoordinates) (e : ContactIndex) :
    pairDerivative q (contactPair e).1 (contactPair e).2 ξ=pairDerivative q e.1 (contactNext e) ξ := by
  unfold contactPair
  by_cases h : e.1≤contactNext e
  · rw [min_eq_left h,max_eq_right h]
  · rw [min_eq_right (le_of_not_ge h),max_eq_left (le_of_not_ge h),pairDerivative_symm]

theorem hessian_positive_contacts_le (p : ℝ) (q ξ : TangentCoordinates) :
    (∑ e : ContactIndex, (tau/squaredDistance (orthographicChart q) e.1 (contactNext e))^(p+2)*
      (pairDerivative q e.1 (contactNext e) ξ)^2)≤hessianPositiveSum p q ξ := by
  have he : (∑ ij∈cyclicContactPairs, (tau/squaredDistance (orthographicChart q) ij.1 ij.2)^(p+2)*
      (pairDerivative q ij.1 ij.2 ξ)^2)=
      ∑ e : ContactIndex, (tau/squaredDistance (orthographicChart q) e.1 (contactNext e))^(p+2)*
        (pairDerivative q e.1 (contactNext e) ξ)^2 := by
    rw [cyclicContactPairs,Finset.sum_image]
    · simp only [contactPair_distance,contactPair_derivative]
    · exact fun a _ b _ h=>contactPair_injective h
  rw [←he]
  apply Finset.sum_le_sum_of_subset_of_nonneg cyclicContactPairs_subset
  intro ij _ _
  exact mul_nonneg (Real.rpow_nonneg (div_nonneg tau_pos.le (sq_nonneg _)) _) (sq_nonneg _)

theorem full_hessian_positive_part (p : ℝ) (hp : (97:ℝ)/2≤p) (q ξ : TangentCoordinates)
    (hq : q∈convexTailDomain p) (hξ : ξ∈rotationSlice) :
    ((329:ℝ)/500)*(p+1)*‖ξ‖^2≤(p+1)*hessianPositiveSum p q ξ := by
  by_cases hξ0 : ξ=0
  · subst ξ
    simp [hessianPositiveSum]
  have hs := derivative_stability_singular_lower p hp q ξ hq hξ hξ0
  have hw : ((7:ℝ)/25)*(∑ e : ContactIndex, (pairDerivative q e.1 (contactNext e) ξ)^2)≤
      ∑ e : ContactIndex, (tau/squaredDistance (orthographicChart q) e.1 (contactNext e))^(p+2)*
        (pairDerivative q e.1 (contactNext e) ξ)^2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun e _=>mul_le_mul_of_nonneg_right
      (contact_weights_hessian_weight p hp q hq e).le (sq_nonneg _))
  have hbase : ((329:ℝ)/500)*‖ξ‖^2≤hessianPositiveSum p q ξ := by
    have h := hw.trans (hessian_positive_contacts_le p q ξ)
    linarith
  have h := mul_le_mul_of_nonneg_left hbase (by linarith : 0≤p+1)
  convert! h using 1 <;> ring

#print axioms full_hessian_positive_part
end Blueprint.Thomson.Tail.Implementation
