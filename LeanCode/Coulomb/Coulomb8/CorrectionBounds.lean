import Coulomb8.Correction

namespace Coulomb8
open scoped BigOperators

def correctionRadius : ℚ := 1/274877906944

theorem correction_exists_from_separate_bounds {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M C : Matrix ι ι ℝ) (r : ι → ℝ)
    (hrow : ∀ i, ∑ j, |(1-C*M) i j| ≤ (1/2 : ℝ))
    (hC : ∀ i, ∑ j, |C i j| ≤ (65536 : ℝ))
    (hr : ‖r‖ ≤ (1/36028797018963968 : ℝ)) :
    ∃ z : ι → ℝ, M.mulVec z=r ∧ ∀ i, |z i| ≤ (correctionRadius : ℝ) := by
  have hcr : ‖C.mulVec r‖ ≤ (1/549755813888 : ℝ) := by
    calc
      _ ≤ 65536*‖r‖ := mulVec_norm_le_row _ _ (by norm_num) hC r
      _ ≤ 65536*(1/36028797018963968 : ℝ) := mul_le_mul_of_nonneg_left hr (by norm_num)
      _ = _ := by norm_num
  obtain ⟨z,hz,hb⟩ := correction_exists M C r (1/549755813888) hrow hcr
  refine ⟨z,hz,fun i => ?_⟩
  convert hb i using 1 <;> norm_num [correctionRadius]

end Coulomb8

#print axioms Coulomb8.correction_exists_from_separate_bounds
