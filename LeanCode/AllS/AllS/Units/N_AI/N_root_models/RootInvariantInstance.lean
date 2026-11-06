import AllS.Units.N_AI.N_data.ArithmeticPilot.RootInvariantRational
import AllS.Units.N_AI.N_elementary_series.N_log_reduction

noncomputable section
namespace Blueprint.CAP
open ArithmeticPilot.RootInvariantRational

def RootInvariantInstanceStatement : Prop :=
  (invariantUpper : ℝ) ≤ Real.log (1+Real.sqrt 2/2)

theorem rootInvariantInstance : RootInvariantInstanceStatement := by
  have hg := rational_gates
  have hr0 : 0 < (sqrtLower : ℝ) := by exact_mod_cast hg.1
  have hr2 : (sqrtLower : ℝ)^2 ≤ 2 := by exact_mod_cast hg.2.1
  have hsr := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hrle : (sqrtLower : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg (2:ℝ)]
  let v : ℝ := 1+(sqrtLower:ℝ)/2
  have hv1 : 1 ≤ v := by dsimp [v]; linarith
  have hu0 : 0 ≤ (u:ℝ) := by exact_mod_cast hg.2.2.1
  have hu1 : (u:ℝ) < 1 := by exact_mod_cast hg.2.2.2.1
  have hu : (u:ℝ) = logTransform v := by simp [u, logTransform, v]
  have hinverse : (1+(u:ℝ))/(1-(u:ℝ)) = v := by
    rw [hu, logTransform_inverse v hv1]
  have hgeo := elementary_series_log_geometric (u:ℝ) 40 hu0 hu1
  rw [hinverse] at hgeo
  have hlower : (lowerLog:ℝ) = 2*logOddPartial 41 (u:ℝ) := by
    simp [lowerLog, logOddPartial]
  have hc : (invariantUpper:ℝ) ≤ (lowerLog:ℝ) := by exact_mod_cast hg.2.2.2.2
  apply hc.trans
  rw [hlower]
  apply hgeo.1.trans
  exact Real.log_le_log (by dsimp [v]; linarith) (by dsimp [v]; linarith)

#print RootInvariantInstanceStatement
#print axioms rootInvariantInstance
end Blueprint.CAP
