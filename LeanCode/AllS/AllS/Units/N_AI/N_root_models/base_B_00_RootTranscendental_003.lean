import AllS.Units.N_AI.N_scalar_models.TranscendentalGateSupport
import AllS.Units.N_AI.N_elementary_series.PointExpSupport
import AllS.Units.N_AI.N_data.ArithmeticPilot.base_B_00_RootError_003
import AllS.Units.N_AI.N_data.ArithmeticPilot.base_B_00_RootExpPoint_010
import AllS.Units.N_AI.N_data.ArithmeticPilot.base_B_00_RootExpPoint_011
import AllS.Units.N_AI.N_data.ArithmeticPilot.base_B_00_RootExpPoint_012
import AllS.Units.N_AI.N_data.ArithmeticPilot.base_B_00_RootExpPoint_014
noncomputable section
namespace Blueprint.CAP.Instances.base_B_00_RootTranscendental_003
open Blueprint.CAP
open Blueprint.CAP.ArithmeticPilot.base_B_00_RootRecurrence_003
open Blueprint.CAP.ArithmeticPilot.base_B_00_RootError_003 (E1 E2)
def Statement : Prop := ∀ f : ℝ → ℝ, input.asTM.Valid f → result.asTM.Valid (fun x => Real.exp (f x))
theorem sound : Statement := by
  intro f hf
  apply QModel.exp_gate_valid input result f E1 E2 hf
  · intro a ha
    have hlo := pointExpSupport Blueprint.CAP.ArithmeticPilot.base_B_00_RootExpPoint_010.enclosure Blueprint.CAP.ArithmeticPilot.base_B_00_RootExpPoint_010.z (66) Blueprint.CAP.ArithmeticPilot.base_B_00_RootExpPoint_010.gate
    have hhi := pointExpSupport Blueprint.CAP.ArithmeticPilot.base_B_00_RootExpPoint_011.enclosure Blueprint.CAP.ArithmeticPilot.base_B_00_RootExpPoint_011.z (66) Blueprint.CAP.ArithmeticPilot.base_B_00_RootExpPoint_011.gate
    change Blueprint.CAP.ArithmeticPilot.base_B_00_RootExpPoint_010.enclosure.asBox.Contains (Real.exp (((input.coeff 0).lo:ℚ):ℝ)) at hlo
    change Blueprint.CAP.ArithmeticPilot.base_B_00_RootExpPoint_011.enclosure.asBox.Contains (Real.exp (((input.coeff 0).hi:ℚ):ℝ)) at hhi
    exact Box.contains_exp_of_endpoints ha hlo hhi (by decide +kernel) (by decide +kernel)
  · exact Blueprint.CAP.ArithmeticPilot.base_B_00_RootRecurrence_003.gate
  · have h := (pointExpSupport Blueprint.CAP.ArithmeticPilot.base_B_00_RootExpPoint_012.enclosure Blueprint.CAP.ArithmeticPilot.base_B_00_RootExpPoint_012.z (37) Blueprint.CAP.ArithmeticPilot.base_B_00_RootExpPoint_012.gate).2
    rw [←(Blueprint.CAP.ArithmeticPilot.base_B_00_RootError_003.point_inputs).1] at h
    exact h
  · have h := (pointExpSupport Blueprint.CAP.ArithmeticPilot.base_B_00_RootExpPoint_014.enclosure Blueprint.CAP.ArithmeticPilot.base_B_00_RootExpPoint_014.z (65) Blueprint.CAP.ArithmeticPilot.base_B_00_RootExpPoint_014.gate).2
    rw [←(Blueprint.CAP.ArithmeticPilot.base_B_00_RootError_003.point_inputs).2] at h
    exact h
  · exact Blueprint.CAP.ArithmeticPilot.base_B_00_RootError_003.gate
#print Statement
#print axioms sound
end Blueprint.CAP.Instances.base_B_00_RootTranscendental_003
