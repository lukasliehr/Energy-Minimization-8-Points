import AllS.Units.N_AI.N_matrix_polynomials.N_bernstein_identity

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def bernsteinControls {d : ℕ} (a : Fin (d+1)→ℝ) (i : Fin (d+1)) : ℝ :=
  ∑ k, (bernsteinTransform d i.val k.val:ℝ)*a k

def bernsteinRadii {d : ℕ} (r : Fin (d+1)→ℝ) (i : Fin (d+1)) : ℝ :=
  ∑ k, |(bernsteinTransform d i.val k.val:ℝ)| * r k

def bernsteinHullBound {d : ℕ} (a r : Fin (d+1)→ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i=>|bernsteinControls a i|+bernsteinRadii r i)

def MatrixBernsteinIntervalStatement : Prop :=
  ∀ (d : ℕ) (a mid rad : Fin (d+1)→ℝ),
    (∀ k, 0 ≤ rad k) → (∀ k, |a k-mid k| ≤ rad k) →
    ∀ x∈cellDomain, |scalarEval a x| ≤ min (bernsteinHullBound mid rad) (∑ k, |a k|)

theorem bernsteinControls_error {d : ℕ} (a mid rad : Fin (d+1)→ℝ)
    (he : ∀ k, |a k-mid k| ≤ rad k) (i : Fin (d+1)) :
    |bernsteinControls a i-bernsteinControls mid i| ≤ bernsteinRadii rad i := by
  unfold bernsteinControls bernsteinRadii
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ k, |(bernsteinTransform d i.val k.val:ℝ)*a k-
        (bernsteinTransform d i.val k.val:ℝ)*mid k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k _
      rw [←mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (he k) (abs_nonneg _)

theorem bernstein_bound_of_controls {d : ℕ} (a : Fin (d+1)→ℝ) (U x : ℝ)
    (hu : ∀ i, |bernsteinControls a i| ≤ U) (hx : x∈cellDomain) :
    |scalarEval a x| ≤ U := by
  rw [matrix_polynomials_bernstein_identity d a x]
  calc
    _ ≤ ∑ i, |bernsteinControls a i*bernsteinWeight d i.val x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (d+1), U*bernsteinWeight d i.val x := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (bernsteinWeight_nonneg d i.val x hx)]
      exact mul_le_mul_of_nonneg_right (hu i) (bernsteinWeight_nonneg d i.val x hx)
    _ = U := by rw [←Finset.mul_sum, bernsteinWeight_sum, mul_one]

theorem matrix_polynomials_bernstein_interval : MatrixBernsteinIntervalStatement := by
  intro d a mid rad hrad he x hx
  apply le_min
  · apply bernstein_bound_of_controls a _ x _ hx
    intro i
    calc
      |bernsteinControls a i| =
          |bernsteinControls mid i+(bernsteinControls a i-bernsteinControls mid i)| := by congr 1; ring
      _ ≤ |bernsteinControls mid i|+|bernsteinControls a i-bernsteinControls mid i| := abs_add_le _ _
      _ ≤ |bernsteinControls mid i|+bernsteinRadii rad i :=
        add_le_add le_rfl (bernsteinControls_error a mid rad he i)
      _ ≤ bernsteinHullBound mid rad := by
        exact Finset.le_sup' (fun j=>|bernsteinControls mid j|+bernsteinRadii rad j) (Finset.mem_univ i)
  · have hxabs : |x| ≤ 1 := abs_le.mpr hx
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro k _
    rw [abs_mul, abs_pow]
    exact (mul_le_mul_of_nonneg_left (pow_le_one₀ (abs_nonneg x) hxabs) (abs_nonneg (a k))).trans_eq
      (mul_one _)

#check matrix_polynomials_bernstein_interval
#print MatrixBernsteinIntervalStatement
#print axioms matrix_polynomials_bernstein_interval
end Blueprint.CAP
