import AllS.Units.N_AI.N_scalar_models.TranscendentalGateSupport
import AllS.Units.N_AI.N_elementary_series.PointExpSupport
import AllS.Units.N_AI.N_elementary_series.ReducedPointExpSupport
import AllS.Units.N_AI.N_data.ArithmeticPilot.finite_d16_c68_RootError_000
import AllS.Units.N_AI.N_data.ArithmeticPilot.finite_d16_c68_RootExpPoint_000
import AllS.Units.N_AI.N_data.ArithmeticPilot.finite_d16_c68_RootExpPoint_001
import AllS.Units.N_AI.N_data.ArithmeticPilot.finite_d16_c68_RootExpPoint_002
import AllS.Units.N_AI.N_data.ArithmeticPilot.finite_d16_c68_RootExpPoint_004
noncomputable section
namespace Blueprint.CAP.Instances.finite_d16_c68_RootTranscendental_000
open Blueprint.CAP
open Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootRecurrence_000
open Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootError_000 (E1 E2)
def Statement : Prop := ∀ f : ℝ → ℝ, input.asTM.Valid f → result.asTM.Valid (fun x => Real.exp (f x))
theorem sound : Statement := by
  intro f hf
  apply QModel.exp_gate_valid input result f E1 E2 hf
  · intro a ha
    have hlo := reducedPointExpSupport Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootExpPoint_000.enclosure Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootExpPoint_000.z (0) (26) Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootExpPoint_000.intervals Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootExpPoint_000.gate
    have hhi := reducedPointExpSupport Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootExpPoint_001.enclosure Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootExpPoint_001.z (0) (26) Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootExpPoint_001.intervals Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootExpPoint_001.gate
    change Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootExpPoint_000.enclosure.asBox.Contains (Real.exp (((input.coeff 0).lo:ℚ):ℝ)) at hlo
    change Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootExpPoint_001.enclosure.asBox.Contains (Real.exp (((input.coeff 0).hi:ℚ):ℝ)) at hhi
    exact Box.contains_exp_of_endpoints ha hlo hhi (by decide +kernel) (by decide +kernel)
  · exact Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootRecurrence_000.gate
  · have h := (reducedPointExpSupport Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootExpPoint_002.enclosure Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootExpPoint_002.z (0) (21) Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootExpPoint_002.intervals Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootExpPoint_002.gate).2
    rw [←(Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootError_000.point_inputs).1] at h
    exact h
  · have h := (reducedPointExpSupport Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootExpPoint_004.enclosure Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootExpPoint_004.z (0) (26) Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootExpPoint_004.intervals Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootExpPoint_004.gate).2
    rw [←(Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootError_000.point_inputs).2] at h
    exact h
  · exact Blueprint.CAP.ArithmeticPilot.finite_d16_c68_RootError_000.gate
#print Statement
#print axioms sound
end Blueprint.CAP.Instances.finite_d16_c68_RootTranscendental_000
