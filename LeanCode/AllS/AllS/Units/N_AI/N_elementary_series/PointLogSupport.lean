import AllS.Units.N_AI.N_data.PointLogGates
import AllS.Units.N_AI.N_scalar_models.ProductGateSupport
import AllS.Units.N_AI.N_elementary_series.N_log_reduction

noncomputable section
open scoped BigOperators
namespace Blueprint.CAP

def PointLogSupportStatement : Prop :=
  ∀ (I : QInterval) (z : ℚ) (r : ℤ) (n : ℕ), I.LogPointGate z r n →
    I.asBox.Contains (Real.log (z:ℝ))

theorem qLogLower_cast (n : ℕ) (v : ℚ) :
    (qLogLower n v:ℝ) = 2*logOddPartial (n+1) (logTransform (v:ℝ)) := by
  simp [qLogLower, logOddPartial, logTransform]

theorem qLogUpper_cast (n : ℕ) (v : ℚ) :
    (qLogUpper n v:ℝ) = 2*logOddPartial (n+1) (logTransform (v:ℝ)) +
      2*(logTransform (v:ℝ))^(2*n+3)/(((2*n+3:ℕ):ℝ)*(1-(logTransform (v:ℝ))^2)) := by
  simp [qLogUpper, qLogLower_cast, logTransform]

theorem qLog_bounds (v : ℚ) (n : ℕ) (hv1 : 1 ≤ v) (hv2 : v ≤ 2) :
    (qLogLower n v:ℝ) ≤ Real.log (v:ℝ) ∧ Real.log (v:ℝ) ≤ (qLogUpper n v:ℝ) := by
  have hg : LogInitialGate (v:ℝ) n ⟨qLogLower n v,qLogUpper n v⟩ := by
    constructor
    · exact (qLogLower_cast n v).le
    · exact (qLogUpper_cast n v).symm.le
  exact Box.contains_log_initial (by exact_mod_cast hv1) (by exact_mod_cast hv2) hg

theorem pointLogSupport : PointLogSupportStatement := by
  intro I z r n hg
  let v : ℚ := z/(2:ℚ)^r
  have hv := qLog_bounds v n hg.2.1 hg.2.2.1
  have ht := qLog_bounds 2 n (by norm_num) le_rfl
  have hlog : Real.log (z:ℝ) = Real.log (v:ℝ)+(r:ℝ)*Real.log 2 := by
    simpa [v] using log_powerTwo_identity (z:ℝ) r (by exact_mod_cast hg.1)
  change (I.lo:ℝ) ≤ Real.log (z:ℝ) ∧ Real.log (z:ℝ) ≤ (I.hi:ℝ)
  rw [hlog]
  by_cases hr : 0 ≤ r
  · have hrR : (0:ℝ) ≤ r := by exact_mod_cast hr
    have hlo : (I.lo:ℝ) ≤ (qLogLower n v:ℝ)+(r:ℝ)*(qLogLower n 2:ℝ) := by
      exact_mod_cast (show I.lo ≤ qLogLower n v+(r:ℚ)*qLogLower n 2 from
        by simpa only [if_pos hr] using hg.2.2.2.1)
    have hhi : (qLogUpper n v:ℝ)+(r:ℝ)*(qLogUpper n 2:ℝ) ≤ (I.hi:ℝ) := by
      exact_mod_cast (show qLogUpper n v+(r:ℚ)*qLogUpper n 2 ≤ I.hi from
        by simpa only [if_pos hr] using hg.2.2.2.2)
    exact ⟨hlo.trans (add_le_add hv.1 (mul_le_mul_of_nonneg_left ht.1 hrR)),
      (add_le_add hv.2 (mul_le_mul_of_nonneg_left ht.2 hrR)).trans hhi⟩
  · have hrR : (r:ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hr)
    have hlo : (I.lo:ℝ) ≤ (qLogLower n v:ℝ)+(r:ℝ)*(qLogUpper n 2:ℝ) := by
      exact_mod_cast (show I.lo ≤ qLogLower n v+(r:ℚ)*qLogUpper n 2 from
        by simpa only [if_neg hr] using hg.2.2.2.1)
    have hhi : (qLogUpper n v:ℝ)+(r:ℝ)*(qLogLower n 2:ℝ) ≤ (I.hi:ℝ) := by
      exact_mod_cast (show qLogUpper n v+(r:ℚ)*qLogLower n 2 ≤ I.hi from
        by simpa only [if_neg hr] using hg.2.2.2.2)
    exact ⟨hlo.trans (add_le_add hv.1 (mul_le_mul_of_nonpos_left ht.2 hrR)),
      (add_le_add hv.2 (mul_le_mul_of_nonpos_left ht.1 hrR)).trans hhi⟩

#check pointLogSupport
#print PointLogSupportStatement
#print axioms pointLogSupport
end Blueprint.CAP
