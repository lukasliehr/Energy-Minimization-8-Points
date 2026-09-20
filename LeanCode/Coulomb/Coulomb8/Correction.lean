import Coulomb8.Interval
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace Coulomb8

open scoped BigOperators

theorem mulVec_norm_le_row {ι : Type*} [Fintype ι]
    (M : Matrix ι ι ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hrow : ∀ i, ∑ j, |M i j| ≤ c) (x : ι → ℝ) :
    ‖M.mulVec x‖ ≤ c*‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hc (norm_nonneg x))).mpr
  intro i
  calc
    ‖M.mulVec x i‖ ≤ ∑ j, ‖M i j*x j‖ := norm_sum_le _ _
    _ ≤ ∑ j, |M i j| * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,Real.norm_eq_abs (M i j)]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x j) (abs_nonneg _)
    _ = (∑ j, |M i j|) * ‖x‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ c*‖x‖ := mul_le_mul_of_nonneg_right (hrow i) (norm_nonneg _)

theorem isUnit_of_half_inverse_error {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M C : Matrix ι ι ℝ)
    (hrow : ∀ i, ∑ j, |(1-C*M) i j| ≤ (1/2 : ℝ)) : IsUnit M := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y hxy
  have hz : M.mulVec (x-y)=0 := by simp [Matrix.mulVec_sub,hxy]
  have he : (1-C*M).mulVec (x-y)=x-y := by
    simp [Matrix.sub_mulVec,←Matrix.mulVec_mulVec,hz]
  have hn := mulVec_norm_le_row (1-C*M) (1/2) (by norm_num) hrow (x-y)
  rw [he] at hn
  have hzero : ‖x-y‖=0 := by linarith [norm_nonneg (x-y)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

theorem correction_exists {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M C : Matrix ι ι ℝ) (r : ι → ℝ) (ε : ℝ)
    (hrow : ∀ i, ∑ j, |(1-C*M) i j| ≤ (1/2 : ℝ))
    (hr : ‖C.mulVec r‖ ≤ ε) :
    ∃ z : ι → ℝ, M.mulVec z=r ∧ ∀ i, |z i| ≤ 2*ε := by
  have hu := isUnit_of_half_inverse_error M C hrow
  obtain ⟨z,hz⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hu) r
  have he : (1-C*M).mulVec z=z-C.mulVec r := by
    simp [Matrix.sub_mulVec,←Matrix.mulVec_mulVec,hz]
  have hb := mulVec_norm_le_row (1-C*M) (1/2) (by norm_num) hrow z
  rw [he] at hb
  have ht : ‖z‖ ≤ ‖C.mulVec r‖+‖z-C.mulVec r‖ := by
    have h := norm_add_le (C.mulVec r) (z-C.mulVec r)
    have heq : C.mulVec r+(z-C.mulVec r)=z := by abel
    rw [heq] at h
    exact h
  have hn : ‖z‖ ≤ 2*ε := by linarith
  refine ⟨z,hz,fun i => ?_⟩
  have hi : |z i| ≤ ‖z‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
  exact hi.trans hn

end Coulomb8

#print axioms Coulomb8.isUnit_of_half_inverse_error
#print axioms Coulomb8.correction_exists
