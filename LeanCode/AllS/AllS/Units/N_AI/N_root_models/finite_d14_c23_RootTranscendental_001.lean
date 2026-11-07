import AllS.Units.N_AI.N_scalar_models.TranscendentalGateSupport
import AllS.Units.N_AI.N_elementary_series.PointExpSupport
import AllS.Units.N_AI.N_data.ArithmeticPilot.finite_d14_c23_RootError_001
import AllS.Units.N_AI.N_data.ArithmeticPilot.finite_d14_c23_RootExpPoint_005
import AllS.Units.N_AI.N_data.ArithmeticPilot.finite_d14_c23_RootExpPoint_006
import AllS.Units.N_AI.N_data.ArithmeticPilot.finite_d14_c23_RootExpPoint_007
import AllS.Units.N_AI.N_data.ArithmeticPilot.finite_d14_c23_RootExpPoint_009
noncomputable section
namespace Blueprint.CAP.Instances.finite_d14_c23_RootTranscendental_001
open Blueprint.CAP
open Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootRecurrence_001
open Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootError_001 (E1 E2)
def Statement : Prop := ∀ f : ℝ → ℝ, input.asTM.Valid f → result.asTM.Valid (fun x => Real.exp (f x))
theorem sound : Statement := by
  intro f hf
  apply QModel.exp_gate_valid input result f E1 E2 hf
  · intro a ha
    have hlo := pointExpSupport Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootExpPoint_005.enclosure Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootExpPoint_005.z (107) Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootExpPoint_005.gate
    have hhi := pointExpSupport Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootExpPoint_006.enclosure Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootExpPoint_006.z (107) Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootExpPoint_006.gate
    change Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootExpPoint_005.enclosure.asBox.Contains (Real.exp (((input.coeff 0).lo:ℚ):ℝ)) at hlo
    change Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootExpPoint_006.enclosure.asBox.Contains (Real.exp (((input.coeff 0).hi:ℚ):ℝ)) at hhi
    exact Box.contains_exp_of_endpoints ha hlo hhi (by decide +kernel) (by decide +kernel)
  · exact Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootRecurrence_001.gate
  · have h := (pointExpSupport Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootExpPoint_007.enclosure Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootExpPoint_007.z (56) Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootExpPoint_007.gate).2
    rw [←(Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootError_001.point_inputs).1] at h
    exact h
  · have h := (pointExpSupport Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootExpPoint_009.enclosure Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootExpPoint_009.z (102) Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootExpPoint_009.gate).2
    rw [←(Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootError_001.point_inputs).2] at h
    exact h
  · exact Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootError_001.gate
#print Statement
#print axioms sound
end Blueprint.CAP.Instances.finite_d14_c23_RootTranscendental_001
