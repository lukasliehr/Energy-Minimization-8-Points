import AllS.Units.N_AI.N_data.ArithmeticPilot.base_B_26_RootCompositionGates
import AllS.Units.N_AI.N_scalar_models.AffineModelSupport
import AllS.Units.N_AI.N_elementary_series.PointLogSupport
import AllS.Units.N_FI.N_root_contraction.N_coordinates

set_option maxHeartbeats 0
set_option maxRecDepth 8192
noncomputable section
namespace Blueprint.CAP.Instances.base_B_26_RootConstants
open Blueprint.CAP Blueprint.Thomson.Finite
open Blueprint.CAP.ArithmeticPilot.base_B_26_RootCompositionGates

def Statement : Prop := rho.asBox.Contains (Real.sqrt 2) ∧
  alpha.asBox.Contains rootAlpha ∧ beta.asBox.Contains rootBeta ∧
  cee.asBox.Contains rootC ∧ logtwo.asBox.Contains (Real.log 2)

theorem rho_contains : rho.asBox.Contains (Real.sqrt 2) := by
  have h := rho_sqrt
  have hlo : (0:ℝ) ≤ rho.lo := by exact_mod_cast h.1
  have hll : (rho.lo:ℝ)^2 ≤ 2 := by exact_mod_cast h.2.1
  have hhh : (2:ℝ) ≤ (rho.hi:ℝ)^2 := by exact_mod_cast h.2.2.1
  have hlh : (rho.lo:ℝ) ≤ rho.hi := by exact_mod_cast h.2.2.2
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hs0 := Real.sqrt_nonneg (2:ℝ)
  change (rho.lo:ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ (rho.hi:ℝ)
  constructor <;> nlinarith

theorem alpha_contains : alpha.asBox.Contains rootAlpha := by
  have h := QInterval.add_contains (QInterval.point_contains 1)
    (QInterval.scale_contains (1/2) rho_contains)
  have he : (1:ℝ)+((1/2:ℚ):ℝ)*Real.sqrt 2 = rootAlpha := by
    norm_num [rootAlpha]; ring
  simp only [Rat.cast_one] at h
  rw [he] at h
  exact QInterval.subset_contains h alpha_interval

theorem beta_contains : beta.asBox.Contains rootBeta := by
  have h := QInterval.add_contains (QInterval.point_contains 1)
    (QInterval.scale_contains (-(1/2)) rho_contains)
  have he : (1:ℝ)+((-(1/2):ℚ):ℝ)*Real.sqrt 2 = rootBeta := by
    norm_num [rootBeta]; ring
  simp only [Rat.cast_one] at h
  rw [he] at h
  exact QInterval.subset_contains h beta_interval

theorem cee_contains : cee.asBox.Contains rootC := by
  have hlo := pointLogSupport Blueprint.CAP.ArithmeticPilot.base_B_26_RootLogPoint_000.enclosure
    Blueprint.CAP.ArithmeticPilot.base_B_26_RootLogPoint_000.z (0) 62 Blueprint.CAP.ArithmeticPilot.base_B_26_RootLogPoint_000.gate
  have hhi := pointLogSupport Blueprint.CAP.ArithmeticPilot.base_B_26_RootLogPoint_001.enclosure
    Blueprint.CAP.ArithmeticPilot.base_B_26_RootLogPoint_001.z (0) 62 Blueprint.CAP.ArithmeticPilot.base_B_26_RootLogPoint_001.gate
  rcases cee_points with ⟨hpos,hloeq,hhieq,hlole,hhile⟩
  rw [hloeq] at hlo
  rw [hhieq] at hhi
  exact Box.contains_log_of_endpoints (by exact_mod_cast hpos) alpha_contains hlo hhi hlole hhile

theorem logtwo_contains : logtwo.asBox.Contains (Real.log 2) := by
  have h := pointLogSupport Blueprint.CAP.ArithmeticPilot.base_B_26_RootLogPoint_002.enclosure
    Blueprint.CAP.ArithmeticPilot.base_B_26_RootLogPoint_002.z (1) 76 Blueprint.CAP.ArithmeticPilot.base_B_26_RootLogPoint_002.gate
  rw [logtwo_point.1] at h
  simpa only [Rat.cast_ofNat] using QInterval.subset_contains h logtwo_point.2

theorem sound : Statement :=
  ⟨rho_contains,alpha_contains,beta_contains,cee_contains,logtwo_contains⟩

theorem rho_valid : rhoM.asTM.Valid (fun _ => Real.sqrt 2) :=
  QModel.const_gate_valid rhoM rho _ rhoM_const rho_contains
theorem cee_valid : ceeM.asTM.Valid (fun _ => rootC) :=
  QModel.const_gate_valid ceeM cee _ ceeM_const cee_contains
theorem beta_valid : betaM.asTM.Valid (fun _ => rootBeta) :=
  QModel.const_gate_valid betaM beta _ betaM_const beta_contains
theorem logtwo_valid : logtwoM.asTM.Valid (fun _ => Real.log 2) :=
  QModel.const_gate_valid logtwoM logtwo _ logtwoM_const logtwo_contains
theorem one_valid : oneM.asTM.Valid (fun _ => 1) := by
  simpa only [Rat.cast_one] using
    QModel.const_gate_valid oneM (QInterval.point 1) _ oneM_const (QInterval.point_contains 1)
theorem two_valid : twoM.asTM.Valid (fun _ => 2) := by
  simpa only [Rat.cast_ofNat] using
    QModel.const_gate_valid twoM (QInterval.point 2) _ twoM_const (QInterval.point_contains 2)
theorem minusTwo_valid : minusTwoM.asTM.Valid (fun _ => -2) := by
  simpa only [Rat.cast_neg, Rat.cast_ofNat] using
    QModel.const_gate_valid minusTwoM (QInterval.point (-2)) _ minusTwoM_const (QInterval.point_contains (-2))

#print Statement
#print axioms sound
#print axioms rho_valid
#print axioms cee_valid
#print axioms beta_valid
#print axioms logtwo_valid
end Blueprint.CAP.Instances.base_B_26_RootConstants
