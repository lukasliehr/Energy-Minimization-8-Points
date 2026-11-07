import AllS.Units.N_AI.N_data.ScalarGates

namespace Blueprint.CAP
open scoped BigOperators

/-- The unique possible second index of a finite convolution coefficient. -/
def qDiagonal {N : ℕ} (f : Fin N → Fin N → ℚ) (k : ℕ) : ℚ :=
  ∑ i, if h : i.val ≤ k ∧ k-i.val < N then f i ⟨k-i.val,h.2⟩ else 0

theorem sum_convolution_diagonal {N : ℕ} (f : Fin N → Fin N → ℚ) (k : ℕ) :
    (∑ i, ∑ j, if i.val+j.val=k then f i j else 0) = qDiagonal f k := by
  unfold qDiagonal
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨k-i.val,h.2⟩ : Fin N)]
    · simp only [show i.val+(k-i.val)=k by omega, if_true]
    · intro j _ hne
      have hij : i.val+j.val ≠ k := by
        intro he
        apply hne
        apply Fin.ext
        dsimp
        omega
      simp only [hij, if_false]
    · simp
  · apply Finset.sum_eq_zero
    intro j _
    have hij : i.val+j.val ≠ k := by omega
    simp only [hij, if_false]

theorem qProductMid_diagonal {n : ℕ} (A B : QModel n) (k : ℕ) :
    qProductMid A B k = qDiagonal
      (fun i j => (A.coeff i).mid*(B.coeff j).mid) k :=
  sum_convolution_diagonal _ _

theorem qProductRad_diagonal {n : ℕ} (A B : QModel n) (k : ℕ) :
    qProductRad A B k = qDiagonal
      (fun i j => |(A.coeff i).mid| * (B.coeff j).rad +
        (A.coeff i).rad * |(B.coeff j).mid| +
        (A.coeff i).rad*(B.coeff j).rad) k :=
  sum_convolution_diagonal _ _

#print axioms sum_convolution_diagonal
#print axioms qProductMid_diagonal
#print axioms qProductRad_diagonal
end Blueprint.CAP
