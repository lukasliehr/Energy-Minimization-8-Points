import AllS.Units.N_AI.N_data.N_polynomial_list

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def EncodingProductBoundStatement : Prop :=
  ∀ {m n p : ℕ} (A : Matrix (Fin m) (Fin n) (List ℤ))
    (B : Matrix (Fin n) (Fin p) (List ℤ)) (L R : ℕ) (MA MB : ℤ),
    0 ≤ MA → 0 ≤ MB → 1 ≤ L → 1 ≤ R →
    (∀ i h, (A i h).length=L) → (∀ h j, (B h j).length=R) →
    (∀ i h a, a∈A i h → |a|≤MA) → (∀ h j b, b∈B h j → |b|≤MB) →
    ∀ i j, (∀ k, |((∑ h, listPolynomial (A i h)*listPolynomial (B h j)) : Polynomial ℤ).coeff k|
      ≤ (n:ℤ)*(min L R:ℕ)*MA*MB) ∧
      ((∑ h, listPolynomial (A i h)*listPolynomial (B h j)) : Polynomial ℤ).natDegree≤L+R-2

theorem listPolynomial_coeff_abs_le (a : List ℤ) (M : ℤ) (hM : 0 ≤ M)
    (ha : ∀ x∈a, |x|≤M) (k : ℕ) : |(listPolynomial a).coeff k|≤M := by
  rw [listPolynomial_coeff]
  split_ifs with hk
  · exact ha _ (List.get_mem _ _)
  · simpa using hM

theorem monomial_mul_coeff_all (p : Polynomial ℤ) (i k : ℕ) (a : ℤ) :
    (Polynomial.monomial i a*p).coeff k =
      if i≤k then a*p.coeff (k-i) else 0 := by
  by_cases hik : i≤k
  · rw [if_pos hik]
    have he : k=k-i+i := by omega
    nth_rw 1 [he]
    exact Polynomial.coeff_monomial_mul p i (k-i) a
  · rw [if_neg hik, ←Polynomial.C_mul_X_pow_eq_monomial, mul_assoc,
      Polynomial.coeff_C_mul, Polynomial.X_pow_mul,
      Polynomial.coeff_mul_X_pow']
    simp [Nat.not_le.mp hik]

theorem listPolynomial_mul_coeff_bound_left (a : List ℤ) (p : Polynomial ℤ)
    (MA MB : ℤ) (hA : 0 ≤ MA) (hB : 0 ≤ MB)
    (ha : ∀ x∈a, |x|≤MA) (hp : ∀ k, |p.coeff k|≤MB) (k : ℕ) :
    |(listPolynomial a*p).coeff k|≤(a.length:ℤ)*MA*MB := by
  classical
  simp only [listPolynomial, Finset.sum_mul, Polynomial.finsetSum_coeff]
  calc
    _ ≤ ∑ i : Fin a.length, |(Polynomial.monomial i.val (a.get i)*p).coeff k| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin a.length, MA*MB := by
      apply Finset.sum_le_sum
      intro i _
      rw [monomial_mul_coeff_all]
      split_ifs
      · rw [abs_mul]
        exact mul_le_mul (ha _ (List.get_mem _ _)) (hp _) (abs_nonneg _) hA
      · simpa using mul_nonneg hA hB
    _ = (a.length:ℤ)*MA*MB := by simp [mul_assoc]

theorem listPolynomial_mul_coeff_bound (a b : List ℤ) (MA MB : ℤ)
    (hA : 0 ≤ MA) (hB : 0 ≤ MB)
    (ha : ∀ x∈a, |x|≤MA) (hb : ∀ x∈b, |x|≤MB) (k : ℕ) :
    |(listPolynomial a*listPolynomial b).coeff k|≤(min a.length b.length:ℕ)*MA*MB := by
  by_cases hab : a.length≤b.length
  · rw [min_eq_left hab]
    exact listPolynomial_mul_coeff_bound_left a _ MA MB hA hB ha
      (listPolynomial_coeff_abs_le b MB hB hb) k
  · rw [min_eq_right (by omega), mul_comm (listPolynomial a)]
    have h := listPolynomial_mul_coeff_bound_left b _ MB MA hB hA hb
      (listPolynomial_coeff_abs_le a MA hA ha) k
    convert h using 1 <;> ring

theorem listPolynomial_natDegree_le (a : List ℤ) :
    (listPolynomial a).natDegree≤a.length-1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [listPolynomial_coeff, dif_neg (by omega)]

theorem encoding_product_bound : EncodingProductBoundStatement := by
  intro m n p A B L R MA MB hMA hMB hL hR hAlen hBlen hA hB i j
  constructor
  · intro k
    rw [Polynomial.finsetSum_coeff]
    calc
      _ ≤ ∑ h : Fin n, |(listPolynomial (A i h)*listPolynomial (B h j)).coeff k| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _h : Fin n, (min L R:ℕ)*MA*MB := by
        apply Finset.sum_le_sum
        intro h _
        simpa only [hAlen,hBlen] using
          listPolynomial_mul_coeff_bound (A i h) (B h j) MA MB hMA hMB (hA i h) (hB h j) k
      _ = (n:ℤ)*(min L R:ℕ)*MA*MB := by simp [mul_assoc]
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro h _
    have ha := listPolynomial_natDegree_le (A i h)
    have hb := listPolynomial_natDegree_le (B h j)
    rw [hAlen] at ha
    rw [hBlen] at hb
    exact Polynomial.natDegree_mul_le.trans ((Nat.add_le_add ha hb).trans (by omega))

#check encoding_product_bound
#print EncodingProductBoundStatement
#print axioms encoding_product_bound
end Blueprint.CAP
