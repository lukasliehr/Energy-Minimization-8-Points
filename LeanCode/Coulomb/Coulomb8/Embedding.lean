import Coulomb8.Witness

namespace Coulomb8
open scoped BigOperators

noncomputable def embedCorrection (z : Fin 99 → ℝ) (c : Fin 192) : ℝ :=
  ∑ j, if Witness.selected j=c then z j else 0

noncomputable def correctedVector (z : Fin 99 → ℝ) (c : Fin 192) : ℝ :=
  Witness.center c+embedCorrection z c

theorem selected_injective : Function.Injective Witness.selected := by decide +kernel

theorem embedCorrection_at (z : Fin 99 → ℝ) (j : Fin 99) :
    embedCorrection z (Witness.selected j)=z j := by
  simp only [embedCorrection,selected_injective.eq_iff]
  simp

theorem embedCorrection_outside (z : Fin 99 → ℝ) (c : Fin 192)
    (h : ∀ j, Witness.selected j ≠ c) : embedCorrection z c=0 := by
  simp [embedCorrection,h]

theorem correctedVector_bound (z : Fin 99 → ℝ)
    (h : ∀ j, |z j| ≤ (correctionRadius : ℝ)) (c : Fin 192) :
    |correctedVector z c-Witness.center c| ≤ (correctionRadius : ℝ) := by
  simp only [correctedVector,add_sub_cancel_left]
  by_cases hc : ∃ j, Witness.selected j=c
  · obtain ⟨j,rfl⟩ := hc
    rw [embedCorrection_at]
    exact h j
  · rw [embedCorrection_outside z c (by simpa using hc)]
    norm_num [correctionRadius]

theorem sum_embedCorrection (A : Fin 192 → ℝ) (z : Fin 99 → ℝ) :
    ∑ c, A c*embedCorrection z c=∑ j, A (Witness.selected j)*z j := by
  simp only [embedCorrection,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [mul_ite,mul_zero]
  simp

theorem correctedVector_equation (A : Matrix (Fin 102) (Fin 192) ℝ) (b : Fin 102 → ℝ)
    (z : Fin 99 → ℝ)
    (hz : ∀ i, ∑ j, A (Witness.rows i) (Witness.selected j)*z j=
      b (Witness.rows i)-∑ c, A (Witness.rows i) c*Witness.center c) (i : Fin 99) :
    ∑ c, A (Witness.rows i) c*correctedVector z c=b (Witness.rows i) := by
  simp only [correctedVector,mul_add,Finset.sum_add_distrib,sum_embedCorrection]
  rw [hz i]
  ring

theorem row_coverage (r : Fin 102) :
    r=0 ∨ r=2 ∨ r=57 ∨ ∃ i, Witness.rows i=r := by
  revert r
  decide +kernel

theorem rows_avoid (i : Fin 99) :
    Witness.rows i ≠ 0 ∧ Witness.rows i ≠ 2 ∧ Witness.rows i ≠ 57 := by
  revert i
  decide +kernel

end Coulomb8

#print axioms Coulomb8.correctedVector_equation
