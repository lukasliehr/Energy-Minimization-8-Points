import AllS.Units.N_AI.N_scalar_models.TranscendentalGateSupport
import AllS.Units.N_AI.N_elementary_series.PointExpSupport
import AllS.Units.N_AI.N_elementary_series.ReducedPointExpSupport
import AllS.Units.N_AI.N_data.ArithmeticPilot.extension_d16_c84_h2_RootError_003
import AllS.Units.N_AI.N_data.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_010
import AllS.Units.N_AI.N_data.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_011
import AllS.Units.N_AI.N_data.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_012
import AllS.Units.N_AI.N_data.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_014
noncomputable section
namespace Blueprint.CAP.Instances.extension_d16_c84_h2_RootTranscendental_003
open Blueprint.CAP
open Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootRecurrence_003
open Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootError_003 (E1 E2)
def Statement : Prop := ∀ f : ℝ → ℝ, input.asTM.Valid f → result.asTM.Valid (fun x => Real.exp (f x))
theorem sound : Statement := by
  intro f hf
  apply QModel.exp_gate_valid input result f E1 E2 hf
  · intro a ha
    have hlo := reducedPointExpSupport Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_010.enclosure Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_010.z (9) (29) Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_010.intervals Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_010.gate
    have hhi := reducedPointExpSupport Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_011.enclosure Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_011.z (9) (29) Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_011.intervals Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_011.gate
    change Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_010.enclosure.asBox.Contains (Real.exp (((input.coeff 0).lo:ℚ):ℝ)) at hlo
    change Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_011.enclosure.asBox.Contains (Real.exp (((input.coeff 0).hi:ℚ):ℝ)) at hhi
    exact Box.contains_exp_of_endpoints ha hlo hhi (by decide +kernel) (by decide +kernel)
  · exact Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootRecurrence_003.gate
  · have h := (reducedPointExpSupport Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_012.enclosure Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_012.z (4) (34) Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_012.intervals Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_012.gate).2
    rw [←(Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootError_003.point_inputs).1] at h
    exact h
  · have h := (reducedPointExpSupport Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_014.enclosure Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_014.z (9) (29) Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_014.intervals Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootExpPoint_014.gate).2
    rw [←(Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootError_003.point_inputs).2] at h
    exact h
  · exact Blueprint.CAP.ArithmeticPilot.extension_d16_c84_h2_RootError_003.gate
#print Statement
#print axioms sound
end Blueprint.CAP.Instances.extension_d16_c84_h2_RootTranscendental_003
