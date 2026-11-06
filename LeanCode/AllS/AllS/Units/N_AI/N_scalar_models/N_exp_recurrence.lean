import AllS.Units.N_AI.N_scalar_models.N_cauchy_low_high
import AllS.Units.N_AI.N_scalar_models.N_segment_variation

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def weightedConvolution {n : ℕ} (a b : Fin (n+1)→ℝ) (m : ℕ) : ℝ :=
  ∑ i, ∑ j, if i.val+j.val=m then (i.val:ℝ)*a i*b j else 0

def expCoefficientRecurrence {n : ℕ} (a c : Fin (n+1)→ℝ) : Prop :=
  ∀ m : Fin (n+1), 0 < m.val → (m.val:ℝ)*c m = weightedConvolution a c m.val

def expResidual {n : ℕ} (a c : Fin (n+1)→ℝ) : Polynomial ℝ :=
  (finitePolynomial c).derivative - (finitePolynomial a).derivative*finitePolynomial c

def ScalarExpRecurrenceStatement : Prop :=
  ∀ {n : ℕ} (a c : Fin (n+1)→ℝ), c 0=Real.exp (a 0) → expCoefficientRecurrence a c →
    (finitePolynomial c).eval 0=Real.exp ((finitePolynomial a).eval 0) ∧
    (∀ k, (expResidual a c).coeff k =
      if k<n then 0 else if k<2*n then -weightedConvolution a c (k+1) else 0)

theorem derivative_mul_finitePolynomial_coeff {n : ℕ}
    (a b : Fin (n+1)→ℝ) (k : ℕ) :
    ((finitePolynomial a).derivative*finitePolynomial b).coeff k =
      weightedConvolution a b (k+1) := by
  classical
  simp only [finitePolynomial, Polynomial.derivative_sum, Polynomial.derivative_monomial,
    Finset.sum_mul, Finset.mul_sum, Polynomial.monomial_mul_monomial,
    Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, weightedConvolution]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hi : i.val=0
  · simp [hi]
  · by_cases hij : i.val-1+j.val=k
    · simp [hij, show i.val+j.val=k+1 by omega, mul_comm, mul_left_comm]
    · simp [hij, show i.val+j.val≠k+1 by omega]

theorem weightedConvolution_eq_zero {n : ℕ} (a b : Fin (n+1)→ℝ)
    (m : ℕ) (hm : 2*n < m) : weightedConvolution a b m=0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hij : i.val+j.val≠m := by have:=i.isLt; have:=j.isLt; omega
  simp [hij]

theorem weightedConvolution_single {n : ℕ} (a b : Fin (n+1)→ℝ) (m : ℕ) :
    weightedConvolution a b m = ∑ i : Fin (n+1),
      if h : i.val ≤ m ∧ m-i.val<n+1 then
        (i.val:ℝ)*a i*b ⟨m-i.val,h.2⟩ else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.val ≤ m ∧ m-i.val<n+1
  · rw [dif_pos hi]
    rw [Finset.sum_eq_single (⟨m-i.val,hi.2⟩ : Fin (n+1))]
    · simp [show i.val+(m-i.val)=m by omega]
    · intro j _ hj
      have hne : i.val+j.val≠m := by
        intro hsum
        apply hj
        apply Fin.ext
        change j.val=m-i.val
        omega
      simp [hne]
    · simp
  · rw [dif_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    have hne : i.val+j.val≠m := by
      intro hsum
      have hj := j.isLt
      apply hi
      constructor <;> omega
    simp [hne]

theorem finitePolynomial_derivative_coeff {n : ℕ} (a : Fin (n+1)→ℝ)
    (k : ℕ) : (finitePolynomial a).derivative.coeff k =
      if h : k<n then (k+1:ℝ)*a ⟨k+1,by omega⟩ else 0 := by
  rw [Polynomial.coeff_derivative, finitePolynomial_coeff]
  by_cases hk : k<n
  · simp [hk, show k+1<n+1 by omega, Nat.cast_add, Nat.cast_one, mul_comm]
  · simp [hk, show ¬k+1<n+1 by omega]

theorem scalar_models_exp_recurrence : ScalarExpRecurrenceStatement := by
  intro n a c hinit hrec
  constructor
  · simpa only [finitePolynomial_eval, scalarEval_at_zero] using hinit
  · intro k
    simp only [expResidual, Polynomial.coeff_sub, finitePolynomial_derivative_coeff,
      derivative_mul_finitePolynomial_coeff]
    by_cases hk : k<n
    · rw [dif_pos hk, if_pos hk]
      have hr := hrec ⟨k+1,by omega⟩ (by simp)
      simp only [Nat.cast_add, Nat.cast_one] at hr
      exact sub_eq_zero.mpr hr
    · rw [dif_neg hk, if_neg hk, zero_sub]
      by_cases hk₂ : k<2*n
      · rw [if_pos hk₂]
      · rw [if_neg hk₂, weightedConvolution_eq_zero a c (k+1) (by omega), neg_zero]

def expResidualCoeffs {n : ℕ} (a c : Fin (n+1)→ℝ) : Fin (2*n)→ℝ :=
  fun k=>if k.val<n then 0 else -weightedConvolution a c (k.val+1)

theorem expResidual_eq_finitePolynomial {n : ℕ} (a c : Fin (n+1)→ℝ)
    (hinit : c 0=Real.exp (a 0)) (hrec : expCoefficientRecurrence a c) :
    expResidual a c = finitePolynomial (expResidualCoeffs a c) := by
  ext k
  rw [(scalar_models_exp_recurrence a c hinit hrec).2 k, finitePolynomial_coeff]
  by_cases hk : k<2*n
  · rw [dif_pos hk]
    simp only [expResidualCoeffs]
    by_cases hkn : k<n <;> simp [hkn,hk]
  · rw [dif_neg hk]
    simp [hk, show ¬k<n by omega]

#check scalar_models_exp_recurrence
#print ScalarExpRecurrenceStatement
#print axioms scalar_models_exp_recurrence
#print axioms expResidual_eq_finitePolynomial
#print axioms weightedConvolution_single
end Blueprint.CAP
