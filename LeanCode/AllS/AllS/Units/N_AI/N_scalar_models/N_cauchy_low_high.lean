import Blueprint.CAPContracts
import AllS.Units.N_AI.N_data.N_polynomial_list

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def finitePolynomial {L : ℕ} (a : Fin L → ℝ) : Polynomial ℝ :=
  ∑ i, Polynomial.monomial i.val (a i)

def cauchyCoeff {n : ℕ} (a b : Fin (n+1) → ℝ) (k : ℕ) : ℝ :=
  ∑ i, ∑ j, if i.val+j.val=k then a i*b j else 0

def cauchyLow {n : ℕ} (a b : Fin (n+1) → ℝ) : Fin (n+1) → ℝ :=
  fun k => cauchyCoeff a b k.val

def cauchyHigh {n : ℕ} (a b : Fin (n+1) → ℝ) : Polynomial ℝ :=
  finitePolynomial (fun k : Fin n => cauchyCoeff a b (n+1+k.val))

def ScalarCauchyLowHighStatement : Prop :=
  ∀ {n : ℕ} (a b : Fin (n+1) → ℝ),
    finitePolynomial a * finitePolynomial b =
      finitePolynomial (cauchyLow a b) + Polynomial.X^(n+1) * cauchyHigh a b

theorem finitePolynomial_coeff {L : ℕ} (a : Fin L → ℝ) (k : ℕ) :
    (finitePolynomial a).coeff k = if h : k<L then a ⟨k,h⟩ else 0 := by
  classical
  simp only [finitePolynomial, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
  by_cases h : k<L
  · rw [dif_pos h]
    rw [Finset.sum_eq_single (⟨k,h⟩ : Fin L)]
    · simp
    · intro b _ hne
      have hv : b.val≠k := fun hh => hne (Fin.ext hh)
      simp [hv, Ne.symm hv]
    · simp
  · rw [dif_neg h]
    apply Finset.sum_eq_zero
    intro b _
    have hv : b.val≠k := by intro hh; have:=b.isLt; omega
    simp [hv, Ne.symm hv]

theorem finitePolynomial_eval {n : ℕ} (a : Fin (n+1)→ℝ) (x : ℝ) :
    (finitePolynomial a).eval x = scalarEval a x := by
  simp [finitePolynomial, scalarEval, Polynomial.eval_finset_sum, Polynomial.eval_monomial]

theorem finitePolynomial_product_coeff {n : ℕ} (a b : Fin (n+1)→ℝ) (k : ℕ) :
    (finitePolynomial a * finitePolynomial b).coeff k = cauchyCoeff a b k := by
  classical
  simp only [finitePolynomial, Finset.sum_mul, Finset.mul_sum,
    Polynomial.monomial_mul_monomial, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, cauchyCoeff]
  rw [Finset.sum_comm]

theorem cauchyCoeff_eq_zero {n : ℕ} (a b : Fin (n+1)→ℝ) (k : ℕ) (hk : 2*n<k) :
    cauchyCoeff a b k = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hij : i.val+j.val≠k := by have:=i.isLt; have:=j.isLt; omega
  simp [hij]

theorem scalar_models_cauchy_low_high : ScalarCauchyLowHighStatement := by
  intro n a b
  ext k
  rw [finitePolynomial_product_coeff, Polynomial.coeff_add, Polynomial.coeff_X_pow_mul',
    finitePolynomial_coeff]
  simp only [cauchyHigh, finitePolynomial_coeff]
  by_cases hk : k<n+1
  · simp [hk, show ¬n+1≤k by omega, cauchyLow]
  · simp only [dif_neg hk, zero_add, if_pos (show n+1≤k by omega)]
    by_cases hk₂ : k-(n+1)<n
    · rw [dif_pos hk₂]
      congr 1
      omega
    · rw [dif_neg hk₂]
      exact cauchyCoeff_eq_zero a b k (by omega)

theorem scalarEval_product_split {n : ℕ} (a b : Fin (n+1)→ℝ) (x : ℝ) :
    scalarEval a x * scalarEval b x = scalarEval (cauchyLow a b) x +
      x^(n+1)*(cauchyHigh a b).eval x := by
  have h := congrArg (fun p : Polynomial ℝ => p.eval x) (scalar_models_cauchy_low_high a b)
  simpa only [Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, finitePolynomial_eval] using h

#check scalar_models_cauchy_low_high
#print ScalarCauchyLowHighStatement
#print axioms scalar_models_cauchy_low_high
end Blueprint.CAP
