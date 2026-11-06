import AllS.Units.N_AI.N_scalar_models.TranscendentalGateSupport
import AllS.Units.N_AI.N_elementary_series.PointExpSupport
import AllS.Units.N_AI.N_data.ArithmeticPilot.extension_d18_c92_h2_RootError_000
import AllS.Units.N_AI.N_data.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_000
import AllS.Units.N_AI.N_data.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_001
import AllS.Units.N_AI.N_data.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_002
import AllS.Units.N_AI.N_data.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_003
import AllS.Units.N_AI.N_root_models.extension_d18_c92_h2_RootExpPoint_000_Sound
import AllS.Units.N_AI.N_root_models.extension_d18_c92_h2_RootExpPoint_001_Sound
import AllS.Units.N_AI.N_root_models.extension_d18_c92_h2_RootExpPoint_002_Sound
import AllS.Units.N_AI.N_root_models.extension_d18_c92_h2_RootExpPoint_003_Sound
noncomputable section
namespace Blueprint.CAP.Instances.extension_d18_c92_h2_RootTranscendental_000
open Blueprint.CAP
open Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootRecurrence_000
open Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootError_000 (E1 E2)
def Statement : Prop := ∀ f : ℝ → ℝ, input.asTM.Valid f → result.asTM.Valid (fun x => Real.exp (f x))
theorem sound : Statement := by
  intro f hf
  apply QModel.exp_gate_valid input result f E1 E2 hf
  · intro a ha
    have hlo := Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_000.sound
    have hhi := Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_001.sound
    change Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_000.enclosure.asBox.Contains (Real.exp (((input.coeff 0).lo:ℚ):ℝ)) at hlo
    change Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_001.enclosure.asBox.Contains (Real.exp (((input.coeff 0).hi:ℚ):ℝ)) at hhi
    exact Box.contains_exp_of_endpoints ha hlo hhi (by decide +kernel) (by decide +kernel)
  · exact Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootRecurrence_000.gate
  · have h := (Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_002.sound).2
    rw [←(Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootError_000.point_inputs).1] at h
    exact h
  · have h := (Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_003.sound).2
    rw [←(Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootError_000.point_inputs).2] at h
    exact h
  · exact Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootError_000.gate
#print Statement
#print axioms sound
end Blueprint.CAP.Instances.extension_d18_c92_h2_RootTranscendental_000
