import AllS.Units.N_AI.N_scalar_models.TranscendentalGateSupport
import AllS.Units.N_AI.N_elementary_series.PointExpSupport
import AllS.Units.N_AI.N_data.ArithmeticPilot.extension_d18_c92_h2_RootError_001
import AllS.Units.N_AI.N_data.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_004
import AllS.Units.N_AI.N_data.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_005
import AllS.Units.N_AI.N_data.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_006
import AllS.Units.N_AI.N_data.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_007
import AllS.Units.N_AI.N_root_models.extension_d18_c92_h2_RootExpPoint_004_Sound
import AllS.Units.N_AI.N_root_models.extension_d18_c92_h2_RootExpPoint_005_Sound
import AllS.Units.N_AI.N_root_models.extension_d18_c92_h2_RootExpPoint_006_Sound
import AllS.Units.N_AI.N_root_models.extension_d18_c92_h2_RootExpPoint_007_Sound
noncomputable section
namespace Blueprint.CAP.Instances.extension_d18_c92_h2_RootTranscendental_001
open Blueprint.CAP
open Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootRecurrence_001
open Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootError_001 (E1 E2)
def Statement : Prop := ∀ f : ℝ → ℝ, input.asTM.Valid f → result.asTM.Valid (fun x => Real.exp (f x))
theorem sound : Statement := by
  intro f hf
  apply QModel.exp_gate_valid input result f E1 E2 hf
  · intro a ha
    have hlo := Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_004.sound
    have hhi := Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_005.sound
    change Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_004.enclosure.asBox.Contains (Real.exp (((input.coeff 0).lo:ℚ):ℝ)) at hlo
    change Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_005.enclosure.asBox.Contains (Real.exp (((input.coeff 0).hi:ℚ):ℝ)) at hhi
    exact Box.contains_exp_of_endpoints ha hlo hhi (by decide +kernel) (by decide +kernel)
  · exact Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootRecurrence_001.gate
  · have h := (Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_006.sound).2
    rw [←(Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootError_001.point_inputs).1] at h
    exact h
  · have h := (Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_007.sound).2
    rw [←(Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootError_001.point_inputs).2] at h
    exact h
  · exact Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootError_001.gate
#print Statement
#print axioms sound
end Blueprint.CAP.Instances.extension_d18_c92_h2_RootTranscendental_001
