import AllS.Units.N_AI.N_scalar_models.TriangularCoefficients
import AllS.Units.N_AI.N_scalar_models.N_exp_recurrence

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def expPrefixStep {n : ℕ} (a : Fin (n+1) → ℝ)
    (k : Fin (n+1)) (b : Fin k.val → ℝ) : ℝ :=
  weightedConvolution a (fun j => if h : j.val < k.val then b ⟨j.val,h⟩ else 0) k.val / k.val

def expCoefficients {n : ℕ} (a : Fin (n+1) → ℝ) : Fin (n+1) → ℝ :=
  triangularCoefficients (Real.exp (a 0)) (expPrefixStep a)

def ExpCoefficientConstructionStatement : Prop :=
  ∀ {n : ℕ} (a : Fin (n+1) → ℝ),
    expCoefficients a 0 = Real.exp (a 0) ∧ expCoefficientRecurrence a (expCoefficients a)

theorem weightedConvolution_prefix {n : ℕ} (a c : Fin (n+1) → ℝ) (k : Fin (n+1)) :
    weightedConvolution a (fun j => if j.val < k.val then c j else 0) k.val =
      weightedConvolution a c k.val := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j.val < k.val
  · simp only [if_pos hj]
  · by_cases hij : i.val+j.val=k.val
    · have hi : i.val=0 := by omega
      simp [hij, hi]
    · simp [hij]

theorem expCoefficients_zero {n : ℕ} (a : Fin (n+1) → ℝ) :
    expCoefficients a 0 = Real.exp (a 0) := triangularCoefficients_zero _ _

theorem expPrefixStep_complete {n : ℕ} (a c : Fin (n+1) → ℝ) (k : Fin (n+1)) :
    expPrefixStep a k (fun i => c ⟨i.val,i.isLt.trans k.isLt⟩) =
      weightedConvolution a c k.val/(k.val:ℝ) := by
  unfold expPrefixStep
  have hf : (fun j : Fin (n+1) => if h : j.val < k.val then
      (fun i : Fin k.val => c ⟨i.val,i.isLt.trans k.isLt⟩) ⟨j.val,h⟩ else 0) =
      (fun j : Fin (n+1) => if j.val < k.val then c j else 0) := by
    funext j
    split_ifs <;> rfl
  rw [hf, weightedConvolution_prefix]

theorem expCoefficients_recurrence {n : ℕ} (a : Fin (n+1) → ℝ) :
    expCoefficientRecurrence a (expCoefficients a) := by
  intro k hk
  have hk0 : k ≠ 0 := by intro h; simpa [h] using hk
  have hcoef : expCoefficients a k =
      weightedConvolution a (expCoefficients a) k.val/(k.val:ℝ) :=
    (triangularCoefficients_step _ _ k hk0).trans (expPrefixStep_complete a (expCoefficients a) k)
  rw [hcoef]
  have hkR : (k.val:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  field_simp

theorem expCoefficients_contains {n : ℕ} (a : Fin (n+1) → ℝ) (R : TM n)
    (hseed : (R.coeff 0).Contains (Real.exp (a 0)))
    (hstep : ∀ k : Fin (n+1), k ≠ 0 → ∀ b : Fin k.val → ℝ,
      (∀ i, (R.coeff ⟨i.val, i.isLt.trans k.isLt⟩).Contains (b i)) →
      (R.coeff k).Contains (expPrefixStep a k b)) :
    R.CoeffContains (expCoefficients a) :=
  triangularCoefficients_contains R _ _ hseed hstep

theorem expCoefficientConstruction : ExpCoefficientConstructionStatement :=
  fun _ => ⟨expCoefficients_zero _,expCoefficients_recurrence _⟩

#check expCoefficientConstruction
#print ExpCoefficientConstructionStatement
#print axioms expCoefficientConstruction
#print axioms expCoefficients_contains
end Blueprint.CAP
