import AllS.Units.N_AI.N_data.PointExpGates
import AllS.Units.N_AI.N_scalar_models.ProductGateSupport
import AllS.Units.N_AI.N_elementary_series.N_exp_reduction

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def PointExpSupportStatement : Prop :=
  ∀ (I : QInterval) (z : ℚ) (n : ℕ), I.ExpPointGate z n →
    I.asBox.Contains (Real.exp (z:ℝ))

theorem qExpTaylor_cast (n : ℕ) (x : ℚ) :
    (qExpTaylor n x:ℝ) = expTaylor n (x:ℝ) := by
  simp [qExpTaylor, expTaylor]

theorem qExpUpper_cast (n : ℕ) (x : ℚ) :
    (qExpUpper n x:ℝ) = expTaylor n (x:ℝ) +
      ((x:ℝ)^(n+1)/(Nat.factorial (n+1):ℝ))/(1-(x:ℝ)/((n:ℝ)+2)) := by
  simp [qExpUpper, qExpTaylor_cast]

theorem pointExpSupport : PointExpSupportStatement := by
  intro I z n hg
  have hab : |(z:ℝ)| < (n:ℝ)+2 := by exact_mod_cast hg.1
  by_cases hz : 0 ≤ z
  · have hzR : (0:ℝ) ≤ z := by exact_mod_cast hz
    have hp := expTail_general (z:ℝ) n hzR (by simpa only [abs_of_nonneg hzR] using hab)
    have he : I.lo ≤ qExpTaylor n z ∧ qExpUpper n z ≤ I.hi := by
      simpa only [if_pos hz] using hg.2
    have hlo : (I.lo:ℝ) ≤ expTaylor n (z:ℝ) := by
      rw [←qExpTaylor_cast]
      exact_mod_cast he.1
    have hhi : expTaylor n (z:ℝ) +
        ((z:ℝ)^(n+1)/(Nat.factorial (n+1):ℝ))/(1-(z:ℝ)/((n:ℝ)+2)) ≤ (I.hi:ℝ) := by
      rw [←qExpUpper_cast]
      exact_mod_cast he.2
    exact ⟨hlo.trans hp.1, hp.2.trans hhi⟩
  · have hzR : (z:ℝ) < 0 := by exact_mod_cast lt_of_not_ge hz
    have hp := exp_negative_enclosure (-(z:ℝ)) n (by linarith)
      (by simpa only [abs_of_neg hzR] using hab)
    have he : I.lo ≤ 1/qExpUpper n (-z) ∧ 1/qExpTaylor n (-z) ≤ I.hi := by
      simpa only [if_neg hz] using hg.2
    have hlo : (I.lo:ℝ) ≤ 1/(qExpUpper n (-z):ℝ) := by exact_mod_cast he.1
    have hhi : 1/(qExpTaylor n (-z):ℝ) ≤ (I.hi:ℝ) := by exact_mod_cast he.2
    rw [qExpUpper_cast, Rat.cast_neg] at hlo
    rw [qExpTaylor_cast, Rat.cast_neg] at hhi
    change (I.lo:ℝ) ≤ Real.exp (z:ℝ) ∧ Real.exp (z:ℝ) ≤ (I.hi:ℝ)
    simpa only [neg_neg] using And.intro (hlo.trans hp.1) (hp.2.trans hhi)

#check pointExpSupport
#print PointExpSupportStatement
#print axioms pointExpSupport
end Blueprint.CAP
