import AllS.Units.N_AI.N_scalar_models.N_exp_recurrence

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def weightedConvolutionExcept {n : ℕ} (a b : Fin (n+1)→ℝ) (m : Fin (n+1)) : ℝ :=
  ∑ i ∈ Finset.univ.erase m, ∑ j,
    if i.val+j.val=m.val then (i.val:ℝ)*a i*b j else 0

def logCoefficientRecurrence {n : ℕ} (a c : Fin (n+1)→ℝ) : Prop :=
  ∀ m : Fin (n+1), 0 < m.val → (m.val:ℝ)*a 0*c m =
    (m.val:ℝ)*a m-weightedConvolutionExcept c a m

def logResidual {n : ℕ} (a c : Fin (n+1)→ℝ) : Polynomial ℝ :=
  finitePolynomial a*(finitePolynomial c).derivative - (finitePolynomial a).derivative

def ScalarLogRecurrenceStatement : Prop :=
  ∀ {n : ℕ} (a c : Fin (n+1)→ℝ), 0<a 0 → c 0=Real.log (a 0) →
    logCoefficientRecurrence a c →
    (finitePolynomial c).eval 0=Real.log ((finitePolynomial a).eval 0) ∧
    (∀ k, (logResidual a c).coeff k =
      if k<n then 0 else if k<2*n then weightedConvolution c a (k+1) else 0)

theorem weightedConvolution_split_last {n : ℕ} (a b : Fin (n+1)→ℝ)
    (m : Fin (n+1)) : weightedConvolution a b m.val =
      (m.val:ℝ)*a m*b 0+weightedConvolutionExcept a b m := by
  classical
  have hin : (∑ j : Fin (n+1), if m.val+j.val=m.val then (m.val:ℝ)*a m*b j else 0) =
      (m.val:ℝ)*a m*b 0 := by
    rw [Finset.sum_eq_single (0:Fin (n+1))]
    · simp
    · intro j _ hj
      have hj₀ : j.val≠0 := fun he=>hj (Fin.ext he)
      simp [hj₀]
    · simp
  have h := Finset.add_sum_erase Finset.univ
    (fun i : Fin (n+1) => ∑ j, if i.val+j.val=m.val then (i.val:ℝ)*a i*b j else 0)
    (Finset.mem_univ m)
  rw [hin] at h
  exact h.symm

theorem logCoefficientRecurrence_weighted {n : ℕ} (a c : Fin (n+1)→ℝ)
    (hrec : logCoefficientRecurrence a c) (m : Fin (n+1)) (hm : 0 < m.val) :
    weightedConvolution c a m.val=(m.val:ℝ)*a m := by
  rw [weightedConvolution_split_last]
  have h := hrec m hm
  nlinarith only [h]

theorem scalar_models_log_recurrence : ScalarLogRecurrenceStatement := by
  intro n a c _ hinit hrec
  constructor
  · simpa only [finitePolynomial_eval, scalarEval_at_zero] using hinit
  · intro k
    simp only [logResidual, Polynomial.coeff_sub, finitePolynomial_derivative_coeff]
    rw [mul_comm (finitePolynomial a), derivative_mul_finitePolynomial_coeff]
    by_cases hk : k<n
    · rw [dif_pos hk, if_pos hk]
      have hr := logCoefficientRecurrence_weighted a c hrec ⟨k+1,by omega⟩ (by simp)
      simp only [Nat.cast_add, Nat.cast_one] at hr
      exact sub_eq_zero.mpr hr
    · rw [dif_neg hk, if_neg hk, sub_zero]
      by_cases hk₂ : k<2*n
      · rw [if_pos hk₂]
      · rw [if_neg hk₂, weightedConvolution_eq_zero c a (k+1) (by omega)]

def logResidualCoeffs {n : ℕ} (a c : Fin (n+1)→ℝ) : Fin (2*n)→ℝ :=
  fun k=>if k.val<n then 0 else weightedConvolution c a (k.val+1)

theorem logResidual_eq_finitePolynomial {n : ℕ} (a c : Fin (n+1)→ℝ)
    (ha : 0<a 0) (hinit : c 0=Real.log (a 0)) (hrec : logCoefficientRecurrence a c) :
    logResidual a c = finitePolynomial (logResidualCoeffs a c) := by
  ext k
  rw [(scalar_models_log_recurrence a c ha hinit hrec).2 k, finitePolynomial_coeff]
  by_cases hk : k<2*n
  · rw [dif_pos hk]
    simp only [logResidualCoeffs]
    by_cases hkn : k<n <;> simp [hkn,hk]
  · rw [dif_neg hk]
    simp [hk, show ¬k<n by omega]

#check scalar_models_log_recurrence
#print ScalarLogRecurrenceStatement
#print axioms scalar_models_log_recurrence
#print axioms logResidual_eq_finitePolynomial
end Blueprint.CAP
