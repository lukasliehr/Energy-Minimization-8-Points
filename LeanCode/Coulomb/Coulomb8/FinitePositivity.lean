import Coulomb8.FiniteBilinear

namespace Coulomb8
open scoped BigOperators

theorem congruence_symm {n : ℕ} (P W : Matrix (Fin n) (Fin n) ℝ)
    (hW : ∀ i j, W i j=W j i) :
    ∀ i j, (P*W*P.transpose) i j=(P*W*P.transpose) j i := by
  have ht : W.transpose=W := by ext i j; exact hW j i
  have h : (P*W*P.transpose).transpose=P*W*P.transpose := by
    simp only [Matrix.transpose_mul,Matrix.transpose_transpose,ht,Matrix.mul_assoc]
  intro i j
  exact congrFun (congrFun h j) i

theorem posDef_of_entry_bounds {n : ℕ} (P W : Matrix (Fin n) (Fin n) ℝ)
    (hn : n ≤ 16) (hW : ∀ i j, W i j=W j i)
    (he : ∀ i j, |(P*W*P.transpose) i j-(if i=j then 1 else 0)| ≤ (1/32 : ℝ)) :
    W.PosDef := by
  apply Thomson8.posDef_of_congruence P W
  apply Thomson8.posDef_of_row_bound _ (congruence_symm P W hW)
  intro i
  calc
    _ ≤ ∑ j : Fin n, (1/32 : ℝ) := Finset.sum_le_sum (fun j _ => he i j)
    _ ≤ 1/2 := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      have hn' : (n : ℝ) ≤ 16 := by exact_mod_cast hn
      linarith

end Coulomb8

#print axioms Coulomb8.posDef_of_entry_bounds
