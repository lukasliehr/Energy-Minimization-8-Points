import AllS.Units.N_AI.N_scalar_models.TranscendentalGateSupport
import AllS.Units.N_AI.N_elementary_series.PointExpSupport
import AllS.Units.N_AI.N_data.ArithmeticPilot.base_B_41_RootError_000
import AllS.Units.N_AI.N_data.ArithmeticPilot.base_B_41_RootExpPoint_000
import AllS.Units.N_AI.N_data.ArithmeticPilot.base_B_41_RootExpPoint_001
import AllS.Units.N_AI.N_data.ArithmeticPilot.base_B_41_RootExpPoint_002
import AllS.Units.N_AI.N_data.ArithmeticPilot.base_B_41_RootExpPoint_004
noncomputable section
namespace Blueprint.CAP.Instances.base_B_41_RootTranscendental_000
open Blueprint.CAP
open Blueprint.CAP.ArithmeticPilot.base_B_41_RootRecurrence_000
open Blueprint.CAP.ArithmeticPilot.base_B_41_RootError_000 (E1 E2)
def Statement : Prop := ∀ f : ℝ → ℝ, input.asTM.Valid f → result.asTM.Valid (fun x => Real.exp (f x))
theorem sound : Statement := by
  intro f hf
  apply QModel.exp_gate_valid input result f E1 E2 hf
  · intro a ha
    have hlo := pointExpSupport Blueprint.CAP.ArithmeticPilot.base_B_41_RootExpPoint_000.enclosure Blueprint.CAP.ArithmeticPilot.base_B_41_RootExpPoint_000.z (34) Blueprint.CAP.ArithmeticPilot.base_B_41_RootExpPoint_000.gate
    have hhi := pointExpSupport Blueprint.CAP.ArithmeticPilot.base_B_41_RootExpPoint_001.enclosure Blueprint.CAP.ArithmeticPilot.base_B_41_RootExpPoint_001.z (34) Blueprint.CAP.ArithmeticPilot.base_B_41_RootExpPoint_001.gate
    change Blueprint.CAP.ArithmeticPilot.base_B_41_RootExpPoint_000.enclosure.asBox.Contains (Real.exp (((input.coeff 0).lo:ℚ):ℝ)) at hlo
    change Blueprint.CAP.ArithmeticPilot.base_B_41_RootExpPoint_001.enclosure.asBox.Contains (Real.exp (((input.coeff 0).hi:ℚ):ℝ)) at hhi
    exact Box.contains_exp_of_endpoints ha hlo hhi (by decide +kernel) (by decide +kernel)
  · exact Blueprint.CAP.ArithmeticPilot.base_B_41_RootRecurrence_000.gate
  · have h := (pointExpSupport Blueprint.CAP.ArithmeticPilot.base_B_41_RootExpPoint_002.enclosure Blueprint.CAP.ArithmeticPilot.base_B_41_RootExpPoint_002.z (21) Blueprint.CAP.ArithmeticPilot.base_B_41_RootExpPoint_002.gate).2
    rw [←(Blueprint.CAP.ArithmeticPilot.base_B_41_RootError_000.point_inputs).1] at h
    exact h
  · have h := (pointExpSupport Blueprint.CAP.ArithmeticPilot.base_B_41_RootExpPoint_004.enclosure Blueprint.CAP.ArithmeticPilot.base_B_41_RootExpPoint_004.z (34) Blueprint.CAP.ArithmeticPilot.base_B_41_RootExpPoint_004.gate).2
    rw [←(Blueprint.CAP.ArithmeticPilot.base_B_41_RootError_000.point_inputs).2] at h
    exact h
  · exact Blueprint.CAP.ArithmeticPilot.base_B_41_RootError_000.gate
#print Statement
#print axioms sound
end Blueprint.CAP.Instances.base_B_41_RootTranscendental_000
