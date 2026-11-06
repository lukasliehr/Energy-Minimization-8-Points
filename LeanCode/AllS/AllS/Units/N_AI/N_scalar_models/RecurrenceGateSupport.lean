import AllS.Units.N_AI.N_data.ScalarRecurrenceGates
import AllS.Units.N_AI.N_scalar_models.IntervalExpressionSupport
import AllS.Units.N_AI.N_scalar_models.ExpCoefficientConstruction
import AllS.Units.N_AI.N_scalar_models.LogCoefficientConstruction

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def RecurrenceGateSupportStatement : Prop :=
  (∀ {n : ℕ} (A R : QModel n) (a : Fin (n+1) → ℝ),
    A.asTM.CoeffContains a → (R.coeff 0).asBox.Contains (Real.exp (a 0)) →
    A.ExpRecurrenceGate R → R.asTM.CoeffContains (expCoefficients a)) ∧
  (∀ {n : ℕ} (A R : QModel n) (a : Fin (n+1) → ℝ),
    A.asTM.CoeffContains a → (R.coeff 0).asBox.Contains (Real.log (a 0)) →
    A.LogRecurrenceGate R → R.asTM.CoeffContains (logCoefficients a))

theorem qWeightedConvolution_contains {n : ℕ} (A B : Fin (n+1) → QInterval)
    (a b : Fin (n+1) → ℝ) (ha : ∀ i, (A i).asBox.Contains (a i))
    (hb : ∀ i, (B i).asBox.Contains (b i)) (m : ℕ) :
    (qWeightedConvolution A B m).asBox.Contains (weightedConvolution a b m) := by
  apply QInterval.sum_contains
  intro i
  apply QInterval.sum_contains
  intro j
  split_ifs
  · simpa only [Rat.cast_natCast] using
      QInterval.mul_contains (QInterval.scale_contains (i.val:ℚ) (ha i)) (hb j)
  · simpa only [Rat.cast_zero] using QInterval.point_contains 0

theorem weightedConvolutionExcept_eq_full {n : ℕ} (a b : Fin (n+1) → ℝ) (m : Fin (n+1)) :
    weightedConvolutionExcept a b m =
      ∑ i, ∑ j, if i ≠ m ∧ i.val+j.val=m.val then (i.val:ℝ)*a i*b j else 0 := by
  unfold weightedConvolutionExcept
  have hf : Finset.univ.erase m = Finset.univ.filter (fun i => i ≠ m) := by
    ext i
    simp
  rw [hf, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ≠ m <;> simp [hi]

theorem qWeightedExcept_contains {n : ℕ} (A B : Fin (n+1) → QInterval)
    (a b : Fin (n+1) → ℝ) (ha : ∀ i, (A i).asBox.Contains (a i))
    (hb : ∀ i, (B i).asBox.Contains (b i)) (m : Fin (n+1)) :
    (qWeightedExcept A B m).asBox.Contains (weightedConvolutionExcept a b m) := by
  rw [weightedConvolutionExcept_eq_full]
  apply QInterval.sum_contains
  intro i
  apply QInterval.sum_contains
  intro j
  split_ifs
  · simpa only [Rat.cast_natCast] using
      QInterval.mul_contains (QInterval.scale_contains (i.val:ℚ) (ha i)) (hb j)
  · simpa only [Rat.cast_zero] using QInterval.point_contains 0

theorem qPrefix_contains {n : ℕ} (R : Fin (n+1) → QInterval) (k : Fin (n+1))
    (b : Fin k.val → ℝ)
    (hb : ∀ i, (R ⟨i.val,i.isLt.trans k.isLt⟩).asBox.Contains (b i)) :
    ∀ j, (qPrefix R k j).asBox.Contains
      (if h : j.val < k.val then b ⟨j.val,h⟩ else 0) := by
  intro j
  unfold qPrefix
  split_ifs with hj
  · exact hb ⟨j.val,hj⟩
  · simpa only [Rat.cast_zero] using QInterval.point_contains 0

theorem QModel.exp_gate_coefficients {n : ℕ} (A R : QModel n) (a : Fin (n+1) → ℝ)
    (ha : A.asTM.CoeffContains a) (hseed : (R.coeff 0).asBox.Contains (Real.exp (a 0)))
    (hg : A.ExpRecurrenceGate R) : R.asTM.CoeffContains (expCoefficients a) := by
  apply expCoefficients_contains a R.asTM hseed
  intro k hk b hb
  have hconv := qWeightedConvolution_contains A.coeff (qPrefix R.coeff k) a
    (fun j => if h : j.val < k.val then b ⟨j.val,h⟩ else 0)
    ha (qPrefix_contains R.coeff k b hb) k.val
  have hout := QInterval.subset_contains
    (QInterval.scale_contains (1/(k.val:ℚ)) hconv) (hg k hk)
  simpa only [expPrefixStep, Rat.cast_div, Rat.cast_one, Rat.cast_natCast,
    one_div_mul_eq_div, QModel.asTM] using hout

theorem QModel.log_gate_coefficients {n : ℕ} (A R : QModel n) (a : Fin (n+1) → ℝ)
    (ha : A.asTM.CoeffContains a) (hseed : (R.coeff 0).asBox.Contains (Real.log (a 0)))
    (hg : A.LogRecurrenceGate R) : R.asTM.CoeffContains (logCoefficients a) := by
  apply logCoefficients_contains a R.asTM hseed
  intro k hk b hb
  have hconv := qWeightedExcept_contains (qPrefix R.coeff k) A.coeff
    (fun j => if h : j.val < k.val then b ⟨j.val,h⟩ else 0) a
    (qPrefix_contains R.coeff k b hb) ha k
  have hden := QInterval.inv_contains (QInterval.scale_contains (k.val:ℚ) (ha 0))
    (Or.inl (hg.2 k hk).1)
  have hnum := QInterval.add_contains (QInterval.scale_contains (k.val:ℚ) (ha k))
    (QInterval.neg_contains hconv)
  have hout := QInterval.subset_contains (QInterval.mul_contains hnum hden) (hg.2 k hk).2
  simpa only [logPrefixStep, Rat.cast_natCast, sub_eq_add_neg, div_eq_mul_inv, one_div,
    one_mul, QModel.asTM] using hout

theorem recurrenceGateSupport : RecurrenceGateSupportStatement :=
  ⟨QModel.exp_gate_coefficients,QModel.log_gate_coefficients⟩

#check recurrenceGateSupport
#print RecurrenceGateSupportStatement
#print axioms recurrenceGateSupport
#print axioms qWeightedConvolution_contains
#print axioms qWeightedExcept_contains
end Blueprint.CAP
