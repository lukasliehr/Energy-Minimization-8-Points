import AllS.Units.N_AI.N_scalar_models.TriangularCoefficients
import AllS.Units.N_AI.N_scalar_models.N_log_recurrence

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def logPrefixStep {n : ℕ} (a : Fin (n+1) → ℝ)
    (k : Fin (n+1)) (b : Fin k.val → ℝ) : ℝ :=
  ((k.val:ℝ)*a k - weightedConvolutionExcept
    (fun j => if h : j.val < k.val then b ⟨j.val,h⟩ else 0) a k) / ((k.val:ℝ)*a 0)

def logCoefficients {n : ℕ} (a : Fin (n+1) → ℝ) : Fin (n+1) → ℝ :=
  triangularCoefficients (Real.log (a 0)) (logPrefixStep a)

def LogCoefficientConstructionStatement : Prop :=
  ∀ {n : ℕ} (a : Fin (n+1) → ℝ), a 0 ≠ 0 →
    logCoefficients a 0 = Real.log (a 0) ∧ logCoefficientRecurrence a (logCoefficients a)

theorem weightedConvolutionExcept_prefix {n : ℕ} (a c : Fin (n+1) → ℝ) (k : Fin (n+1)) :
    weightedConvolutionExcept (fun j => if j.val < k.val then c j else 0) a k =
      weightedConvolutionExcept c a k := by
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j _
  by_cases hik : i.val < k.val
  · simp only [if_pos hik]
  · have hikne : i.val ≠ k.val := fun he => (Finset.mem_erase.mp hi).1 (Fin.ext he)
    have hij : i.val+j.val ≠ k.val := by omega
    simp only [if_neg hij]

theorem logCoefficients_zero {n : ℕ} (a : Fin (n+1) → ℝ) :
    logCoefficients a 0 = Real.log (a 0) := triangularCoefficients_zero _ _

theorem logPrefixStep_complete {n : ℕ} (a c : Fin (n+1) → ℝ) (k : Fin (n+1)) :
    logPrefixStep a k (fun i => c ⟨i.val,i.isLt.trans k.isLt⟩) =
      ((k.val:ℝ)*a k-weightedConvolutionExcept c a k)/((k.val:ℝ)*a 0) := by
  unfold logPrefixStep
  have hf : (fun j : Fin (n+1) => if h : j.val < k.val then
      (fun i : Fin k.val => c ⟨i.val,i.isLt.trans k.isLt⟩) ⟨j.val,h⟩ else 0) =
      (fun j : Fin (n+1) => if j.val < k.val then c j else 0) := by
    funext j
    split_ifs <;> rfl
  rw [hf, weightedConvolutionExcept_prefix]

theorem logCoefficients_recurrence {n : ℕ} (a : Fin (n+1) → ℝ) (ha : a 0 ≠ 0) :
    logCoefficientRecurrence a (logCoefficients a) := by
  intro k hk
  have hk0 : k ≠ 0 := by intro h; simpa [h] using hk
  have hcoef : logCoefficients a k =
      ((k.val:ℝ)*a k-weightedConvolutionExcept (logCoefficients a) a k)/((k.val:ℝ)*a 0) :=
    (triangularCoefficients_step _ _ k hk0).trans (logPrefixStep_complete a (logCoefficients a) k)
  rw [hcoef]
  have hkR : (k.val:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  field_simp

theorem logCoefficients_contains {n : ℕ} (a : Fin (n+1) → ℝ) (R : TM n)
    (hseed : (R.coeff 0).Contains (Real.log (a 0)))
    (hstep : ∀ k : Fin (n+1), k ≠ 0 → ∀ b : Fin k.val → ℝ,
      (∀ i, (R.coeff ⟨i.val, i.isLt.trans k.isLt⟩).Contains (b i)) →
      (R.coeff k).Contains (logPrefixStep a k b)) :
    R.CoeffContains (logCoefficients a) :=
  triangularCoefficients_contains R _ _ hseed hstep

theorem logCoefficientConstruction : LogCoefficientConstructionStatement :=
  fun a ha => ⟨logCoefficients_zero a,logCoefficients_recurrence a ha⟩

#check logCoefficientConstruction
#print LogCoefficientConstructionStatement
#print axioms logCoefficientConstruction
#print axioms logCoefficients_contains
end Blueprint.CAP
