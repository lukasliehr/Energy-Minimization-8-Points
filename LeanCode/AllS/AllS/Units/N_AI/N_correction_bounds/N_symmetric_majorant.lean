import AllS.Units.N_AI.N_correction_bounds.N_weighted_quadratic

namespace Blueprint.CAP
def CorrectionSymmetricMajorantStatement : Prop :=
  ∀ {n : ℕ} (E M : Matrix (Fin n) (Fin n) ℝ),
    (∀ i j, E i j=E j i) → (∀ i j, |E i j| ≤ M i j) →
    (∀ i j, |E i j| ≤ min (M i j) (M j i)) ∧
    (∀ i j, min (M i j) (M j i)=min (M j i) (M i j)) ∧
    (∀ i j, 0 ≤ min (M i j) (M j i))

theorem correction_bounds_symmetric_majorant : CorrectionSymmetricMajorantStatement := by
  intro n E M hsym hbound
  have hm : ∀ i j, |E i j| ≤ min (M i j) (M j i) := by
    intro i j
    apply le_min (hbound i j)
    rw [hsym i j]
    exact hbound j i
  exact ⟨hm, fun i j=>min_comm _ _, fun i j=>(abs_nonneg _).trans (hm i j)⟩

#check correction_bounds_symmetric_majorant
#print CorrectionSymmetricMajorantStatement
#print axioms correction_bounds_symmetric_majorant
end Blueprint.CAP
