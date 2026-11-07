import Blueprint.CAPContracts
import Blueprint.Target

/-! Full ascending coefficient lists; work card AI.data.polynomial_list. -/
noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def listPolynomial {R : Type*} [Semiring R] (L : List R) : Polynomial R :=
  ∑ k : Fin L.length, Polynomial.monomial k.val (L.get k)

def DataPolynomialListStatement : Prop :=
  (∀ (L : List ℚ) (x : ℝ), evalQPoly (listPolynomial L) x =
    ∑ k : Fin L.length, (L.get k : ℝ) * x ^ k.val) ∧
  (∀ (L : List ℚ) (padding : ℕ),
    listPolynomial (L ++ List.replicate padding 0) = listPolynomial L)

theorem listPolynomial_eval (L : List ℚ) (x : ℝ) :
    evalQPoly (listPolynomial L) x =
      ∑ k : Fin L.length, (L.get k : ℝ) * x ^ k.val := by
  simp [evalQPoly, listPolynomial, Polynomial.eval₂_finsetSum]

theorem listPolynomial_coeff {R : Type*} [Semiring R] (L : List R) (n : ℕ) :
    (listPolynomial L).coeff n = if hn : n < L.length then L.get ⟨n, hn⟩ else 0 := by
  classical
  by_cases hn : n < L.length
  · simp only [listPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single ⟨n, hn⟩]
    · simp [hn]
    · intro b hb hbn
      have hbval : b.val ≠ n := by
        intro heq
        apply hbn
        exact Fin.ext heq
      simp [hbval]
    · simp
  · simp only [listPolynomial, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_zero]
    · simp [hn]
    · intro b hb
      have hbval : b.val ≠ n := by
        intro heq
        exact hn (heq ▸ b.isLt)
      simp [hbval]

theorem listPolynomial_zeroPadding {R : Type*} [Semiring R] (L : List R)
    (padding : ℕ) :
    listPolynomial (L ++ List.replicate padding 0) = listPolynomial L := by
  ext n
  rw [listPolynomial_coeff, listPolynomial_coeff]
  by_cases hn : n < L.length
  · have hnp : n < (L ++ List.replicate padding 0).length := by
      simp only [List.length_append, List.length_replicate]
      omega
    rw [dif_pos hnp, dif_pos hn]
    simp only [List.get_eq_getElem, List.getElem_append_left hn]
  · by_cases hnp : n < (L ++ List.replicate padding 0).length
    · rw [dif_pos hnp, dif_neg hn]
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_right (by omega)]
      simp
    · rw [dif_neg hnp, dif_neg hn]

theorem data_polynomial_list : DataPolynomialListStatement :=
  ⟨listPolynomial_eval, listPolynomial_zeroPadding⟩

#check data_polynomial_list
#print data_polynomial_list
#print axioms data_polynomial_list
#print axioms listPolynomial_coeff
end Blueprint.CAP
