import Coulomb8.ReducedSolution
import Coulomb8.Annihilators
import Coulomb8.TargetAnnihilators
import Coulomb8.LinearCompletion

namespace Coulomb8
open scoped BigOperators
open Annihilators

theorem complete_coefficient_equations (w : Fin 192 → ℝ)
    (hw : ∀ i : Fin 99, ∑ c, CoefficientMatrix.matrix (Witness.rows i) c*w c=target (Witness.rows i)) :
    ∀ r, ∑ c, CoefficientMatrix.matrix r c*w c=target r := by
  let E (r : Fin 102) := target r-∑ c, CoefficientMatrix.matrix r c*w c
  have he (r : Fin 102) (h0 : r ≠ 0) (h2 : r ≠ 2) (h57 : r ≠ 57) : E r=0 := by
    obtain h | h | h | ⟨i,hi⟩ := row_coverage r
    · exact (h0 h).elim
    · exact (h2 h).elim
    · exact (h57 h).elim
    · subst r
      simp only [E,hw i,sub_self]
  have h57 : E 57=0 := by
    simp only [E,target_structural_zero,structural_zero,zero_mul,Finset.sum_const_zero,sub_self]
  have hL0 : ∑ r, L0 r*E r=0 := functional_residual _ _ _ w annihilates0 target0
  have hL1 : ∑ r, L1 r*E r=0 := functional_residual _ _ _ w annihilates1 target1
  rw [sum_three_support L1 E he,constant1,h57,zero_mul,mul_zero,zero_add,add_zero] at hL1
  have h2 : E 2=0 := (mul_eq_zero.mp hL1).resolve_left quadratic1_nonzero
  rw [sum_three_support L0 E he,constant0,h2,h57,mul_zero,mul_zero,add_zero,add_zero] at hL0
  have h0 : E 0=0 := by linarith
  intro r
  have hEr : E r=0 := by
    obtain rfl | rfl | rfl | ⟨i,hi⟩ := row_coverage r
    · exact h0
    · exact h2
    · exact h57
    · subst r; simp only [E,hw i,sub_self]
  exact (sub_eq_zero.mp hEr).symm

theorem full_solution : ∃ w : Fin 192 → ℝ,
    (∀ c, |w c-Witness.center c| ≤ (correctionRadius : ℝ)) ∧
    ∀ r, ∑ c, CoefficientMatrix.matrix r c*w c=target r := by
  obtain ⟨w,hb,hw⟩ := reduced_solution
  exact ⟨w,hb,complete_coefficient_equations w hw⟩

end Coulomb8

#print axioms Coulomb8.full_solution
