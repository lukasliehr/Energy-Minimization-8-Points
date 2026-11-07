import AllS.Units.N_AI.N_scalar_models.TranscendentalGateSupport
import AllS.Units.N_AI.N_elementary_series.PointLogSupport
import AllS.Units.N_AI.N_data.ArithmeticPilot.base_B_35_RootError_002
import AllS.Units.N_AI.N_data.ArithmeticPilot.base_B_35_RootLogPoint_003
import AllS.Units.N_AI.N_data.ArithmeticPilot.base_B_35_RootLogPoint_004
noncomputable section
namespace Blueprint.CAP.Instances.base_B_35_RootTranscendental_002
open Blueprint.CAP
open Blueprint.CAP.ArithmeticPilot.base_B_35_RootRecurrence_002
def Statement : Prop := ∀ f : ℝ → ℝ, input.asTM.Valid f → result.asTM.Valid (fun x => Real.log (f x))
theorem sound : Statement := by
  intro f hf
  apply QModel.log_gate_valid input result f hf
  · intro a ha
    have hlo := pointLogSupport Blueprint.CAP.ArithmeticPilot.base_B_35_RootLogPoint_003.enclosure Blueprint.CAP.ArithmeticPilot.base_B_35_RootLogPoint_003.z (1) (76) Blueprint.CAP.ArithmeticPilot.base_B_35_RootLogPoint_003.gate
    have hhi := pointLogSupport Blueprint.CAP.ArithmeticPilot.base_B_35_RootLogPoint_004.enclosure Blueprint.CAP.ArithmeticPilot.base_B_35_RootLogPoint_004.z (1) (76) Blueprint.CAP.ArithmeticPilot.base_B_35_RootLogPoint_004.gate
    change Blueprint.CAP.ArithmeticPilot.base_B_35_RootLogPoint_003.enclosure.asBox.Contains (Real.log (((input.coeff 0).lo:ℚ):ℝ)) at hlo
    change Blueprint.CAP.ArithmeticPilot.base_B_35_RootLogPoint_004.enclosure.asBox.Contains (Real.log (((input.coeff 0).hi:ℚ):ℝ)) at hhi
    have hpos : (0:ℝ) < ((input.coeff 0).lo:ℝ) := by exact_mod_cast (Blueprint.CAP.ArithmeticPilot.base_B_35_RootRecurrence_002.gate).1
    exact Box.contains_log_of_endpoints hpos ha hlo hhi (by decide +kernel) (by decide +kernel)
  · exact Blueprint.CAP.ArithmeticPilot.base_B_35_RootRecurrence_002.gate
  · exact Blueprint.CAP.ArithmeticPilot.base_B_35_RootError_002.gate
#print Statement
#print axioms sound
end Blueprint.CAP.Instances.base_B_35_RootTranscendental_002
