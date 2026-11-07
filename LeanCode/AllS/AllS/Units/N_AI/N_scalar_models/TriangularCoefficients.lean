import Blueprint.CAPContracts

noncomputable section
namespace Blueprint.CAP

/- A finite coefficient recurrence. The prefix argument has exactly k entries,
   so a recurrence cannot read the coefficient currently being defined. -/
def triangularCoefficients {n : ℕ} (seed : ℝ)
    (step : (k : Fin (n+1)) → (Fin k.val → ℝ) → ℝ) (k : Fin (n+1)) : ℝ :=
  if h : k = 0 then seed else
    step k (fun i => triangularCoefficients seed step ⟨i.val, i.isLt.trans k.isLt⟩)
termination_by k.val

def TriangularCoefficientsStatement : Prop :=
  ∀ {n : ℕ} (R : TM n) (seed : ℝ)
    (step : (k : Fin (n+1)) → (Fin k.val → ℝ) → ℝ),
    (R.coeff 0).Contains seed →
    (∀ k : Fin (n+1), k ≠ 0 → ∀ b : Fin k.val → ℝ,
      (∀ i, (R.coeff ⟨i.val, i.isLt.trans k.isLt⟩).Contains (b i)) →
      (R.coeff k).Contains (step k b)) →
    R.CoeffContains (triangularCoefficients seed step) ∧
    triangularCoefficients seed step 0 = seed ∧
    ∀ k : Fin (n+1), k ≠ 0 → triangularCoefficients seed step k =
      step k (fun i => triangularCoefficients seed step ⟨i.val, i.isLt.trans k.isLt⟩)

theorem triangularCoefficients_zero {n : ℕ} (seed : ℝ)
    (step : (k : Fin (n+1)) → (Fin k.val → ℝ) → ℝ) :
    triangularCoefficients seed step 0 = seed := by
  rw [triangularCoefficients]
  simp

theorem triangularCoefficients_step {n : ℕ} (seed : ℝ)
    (step : (k : Fin (n+1)) → (Fin k.val → ℝ) → ℝ)
    (k : Fin (n+1)) (hk : k ≠ 0) :
    triangularCoefficients seed step k =
      step k (fun i => triangularCoefficients seed step ⟨i.val, i.isLt.trans k.isLt⟩) := by
  rw [triangularCoefficients, dif_neg hk]

theorem triangularCoefficients_contains {n : ℕ} (R : TM n) (seed : ℝ)
    (step : (k : Fin (n+1)) → (Fin k.val → ℝ) → ℝ)
    (hseed : (R.coeff 0).Contains seed)
    (hstep : ∀ k : Fin (n+1), k ≠ 0 → ∀ b : Fin k.val → ℝ,
      (∀ i, (R.coeff ⟨i.val, i.isLt.trans k.isLt⟩).Contains (b i)) →
      (R.coeff k).Contains (step k b)) :
    R.CoeffContains (triangularCoefficients seed step) := by
  intro k
  have h (m : ℕ) : ∀ hm : m < n+1,
      (R.coeff ⟨m,hm⟩).Contains (triangularCoefficients seed step ⟨m,hm⟩) := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro hm
      by_cases hz : (⟨m,hm⟩ : Fin (n+1)) = 0
      · simpa only [hz, triangularCoefficients_zero] using hseed
      · rw [triangularCoefficients_step seed step _ hz]
        apply hstep _ hz
        intro i
        exact ih i.val i.isLt (i.isLt.trans hm)
  exact h k.val k.isLt

theorem triangularCoefficients_sound : TriangularCoefficientsStatement := by
  intro n R seed step hseed hstep
  exact ⟨triangularCoefficients_contains R seed step hseed hstep,
    triangularCoefficients_zero seed step, triangularCoefficients_step seed step⟩

#check triangularCoefficients_sound
#print TriangularCoefficientsStatement
#print axioms triangularCoefficients_sound
end Blueprint.CAP
