import AllS.Units.N_AI.N_data.ScalarErrorGates
import AllS.Units.N_AI.N_scalar_models.RecurrenceGateSupport
import AllS.Units.N_AI.N_scalar_models.N_exp_input_error
import AllS.Units.N_AI.N_scalar_models.N_log_input_error

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def TranscendentalGateSupportStatement : Prop :=
  (∀ {n : ℕ} (A R : QModel n) (f : ℝ → ℝ) (E₁ E₂ : ℚ),
    A.asTM.Valid f →
    (∀ a : ℝ, (A.coeff 0).asBox.Contains a → (R.coeff 0).asBox.Contains (Real.exp a)) →
    A.ExpRecurrenceGate R → Real.exp (A.variation:ℝ) ≤ (E₁:ℝ) →
    Real.exp (A.hull.hi:ℝ) ≤ (E₂:ℝ) → A.ExpErrorGate R E₁ E₂ →
    R.asTM.Valid (fun x => Real.exp (f x))) ∧
  (∀ {n : ℕ} (A R : QModel n) (f : ℝ → ℝ),
    A.asTM.Valid f →
    (∀ a : ℝ, (A.coeff 0).asBox.Contains a → (R.coeff 0).asBox.Contains (Real.log a)) →
    A.LogRecurrenceGate R → A.LogErrorGate R → R.asTM.Valid (fun x => Real.log (f x)))

theorem QInterval.abs_le_mag {I : QInterval} {x : ℝ} (hx : I.asBox.Contains x) :
    |x| ≤ (I.mag:ℝ) := by
  simpa only [Box.magnitude, QInterval.mag, QInterval.asBox] using Box.abs_le_magnitude hx

theorem QModel.variation_bound {n : ℕ} (A : QModel n) (a : Fin (n+1) → ℝ)
    (ha : A.asTM.CoeffContains a) : coefficientVariation a ≤ (A.variation:ℝ) := by
  unfold coefficientVariation QModel.variation
  rw [Rat.cast_sum]
  exact Finset.sum_le_sum (fun k _ => QInterval.abs_le_mag (ha k))

theorem qIntegrated_exp_bound {n : ℕ} (A R : QModel n) (a c : Fin (n+1) → ℝ)
    (ha : A.asTM.CoeffContains a) (hc : R.asTM.CoeffContains c) :
    (∑ k, |expResidualCoeffs a c k|/(k.val+1)) ≤ (qIntegratedDefect A R:ℝ) := by
  simp only [qIntegratedDefect, Rat.cast_sum, apply_ite, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_zero]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k.val < n
  · simp [expResidualCoeffs, hk, show ¬n ≤ k.val by omega]
  · simp only [expResidualCoeffs, if_neg hk, if_pos (show n ≤ k.val by omega), abs_neg]
    have hb := QInterval.abs_le_mag (qWeightedConvolution_contains A.coeff R.coeff a c ha hc (k.val+1))
    simpa only [Nat.cast_add, Nat.cast_one] using
      div_le_div_of_nonneg_right hb (show (0:ℝ) ≤ ((k.val+1:ℕ):ℝ) by positivity)

theorem qIntegrated_log_bound {n : ℕ} (A R : QModel n) (a c : Fin (n+1) → ℝ)
    (ha : A.asTM.CoeffContains a) (hc : R.asTM.CoeffContains c) :
    (∑ k, |logResidualCoeffs a c k|/(k.val+1)) ≤ (qIntegratedDefect R A:ℝ) := by
  simp only [qIntegratedDefect, Rat.cast_sum, apply_ite, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_zero]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k.val < n
  · simp [logResidualCoeffs, hk, show ¬n ≤ k.val by omega]
  · simp only [logResidualCoeffs, if_neg hk, if_pos (show n ≤ k.val by omega)]
    have hb := QInterval.abs_le_mag (qWeightedConvolution_contains R.coeff A.coeff c a hc ha (k.val+1))
    simpa only [Nat.cast_add, Nat.cast_one] using
      div_le_div_of_nonneg_right hb (show (0:ℝ) ≤ ((k.val+1:ℕ):ℝ) by positivity)

theorem QModel.hull_positive {n : ℕ} (A : QModel n) (he : 0 ≤ A.error)
    (hμ : 0 < A.hull.lo) : A.asTM.CommonPositiveHull A.hull.asBox A.hull.lo := by
  apply scalar_models_log_common_hull A.asTM A.hull.asBox A.hull.lo he hμ le_rfl
  exact ⟨le_rfl,le_rfl⟩

theorem QModel.exp_gate_valid {n : ℕ} (A R : QModel n) (f : ℝ → ℝ) (E₁ E₂ : ℚ)
    (hA : A.asTM.Valid f)
    (hseed : ∀ a : ℝ, (A.coeff 0).asBox.Contains a → (R.coeff 0).asBox.Contains (Real.exp a))
    (hg : A.ExpRecurrenceGate R) (hE₁ : Real.exp (A.variation:ℝ) ≤ (E₁:ℝ))
    (hE₂ : Real.exp (A.hull.hi:ℝ) ≤ (E₂:ℝ)) (he : A.ExpErrorGate R E₁ E₂) :
    R.asTM.Valid (fun x => Real.exp (f x)) := by
  rcases hA with ⟨heA,a,ha,hra⟩
  let w : A.asTM.Witness f := ⟨a,ha,heA,hra⟩
  let c := expCoefficients a
  have hc : R.asTM.CoeffContains c := A.exp_gate_coefficients R a ha (hseed _ (ha 0)) hg
  have hinit := (scalar_models_exp_recurrence a c (expCoefficients_zero a)
    (expCoefficients_recurrence a)).1
  have hres := expResidual_eq_finitePolynomial a c (expCoefficients_zero a) (expCoefficients_recurrence a)
  apply scalar_models_exp_input_error A.asTM R.asTM f w c (expResidualCoeffs a c) hc hinit hres
  have hD := qIntegrated_exp_bound A R a c ha hc
  have hV := A.variation_bound a ha
  have hE₁' : Real.exp (coefficientVariation a) ≤ (E₁:ℝ) :=
    (Real.exp_le_exp.mpr hV).trans hE₁
  have harg : a 0+coefficientVariation a+(A.error:ℝ) ≤ (A.hull.hi:ℝ) := by
    have h0 := (ha 0).2
    change a 0 ≤ ((A.coeff 0).hi:ℝ) at h0
    simpa [QModel.hull] using add_le_add (add_le_add h0 hV) (le_refl (A.error:ℝ))
  have hE₂' := (Real.exp_le_exp.mpr harg).trans hE₂
  have hE₁0 : (0:ℝ) ≤ E₁ := (Real.exp_pos _).le.trans hE₁
  have hD0 : (0:ℝ) ≤ ∑ k, |expResidualCoeffs a c k|/(k.val+1) :=
    Finset.sum_nonneg (fun k _ => div_nonneg (abs_nonneg _) (by positivity))
  have heAR : (0:ℝ) ≤ A.error := by exact_mod_cast heA
  have hb := add_le_add (mul_le_mul hE₁' hD hD0 hE₁0)
    (mul_le_mul_of_nonneg_right hE₂' heAR)
  exact hb.trans (by exact_mod_cast he)

theorem QModel.log_gate_valid {n : ℕ} (A R : QModel n) (f : ℝ → ℝ)
    (hA : A.asTM.Valid f)
    (hseed : ∀ a : ℝ, (A.coeff 0).asBox.Contains a → (R.coeff 0).asBox.Contains (Real.log a))
    (hg : A.LogRecurrenceGate R) (he : A.LogErrorGate R) :
    R.asTM.Valid (fun x => Real.log (f x)) := by
  rcases hA with ⟨heA,a,ha,hra⟩
  let w : A.asTM.Witness f := ⟨a,ha,heA,hra⟩
  let c := logCoefficients a
  have hc : R.asTM.CoeffContains c := A.log_gate_coefficients R a ha (hseed _ (ha 0)) hg
  have hA0 : (0:ℝ) < (A.coeff 0).lo := by exact_mod_cast hg.1
  have ha0 : 0 < a 0 := hA0.trans_le (ha 0).1
  have hrec := logCoefficients_recurrence a ha0.ne'
  have hinit := (scalar_models_log_recurrence a c ha0 (logCoefficients_zero a) hrec).1
  have hres := logResidual_eq_finitePolynomial a c ha0 (logCoefficients_zero a) hrec
  apply scalar_models_log_input_error A.asTM R.asTM f w c (logResidualCoeffs a c)
    A.hull.asBox A.hull.lo (A.hull_positive heA he.1) hc hinit hres
  have hD := qIntegrated_log_bound A R a c ha hc
  have hμ : (0:ℝ) ≤ A.hull.lo := by exact_mod_cast he.1.le
  have hb := div_le_div_of_nonneg_right (add_le_add hD (le_refl (A.error:ℝ))) hμ
  exact hb.trans (by exact_mod_cast he.2)

theorem transcendentalGateSupport : TranscendentalGateSupportStatement :=
  ⟨QModel.exp_gate_valid,QModel.log_gate_valid⟩

#check transcendentalGateSupport
#print TranscendentalGateSupportStatement
#print axioms transcendentalGateSupport
end Blueprint.CAP
