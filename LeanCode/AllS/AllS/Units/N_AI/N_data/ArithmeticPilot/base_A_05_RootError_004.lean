import AllS.Units.N_AI.N_data.ScalarErrorGates
import AllS.Units.N_AI.N_data.ArithmeticPilot.base_A_05_RootRecurrence_004
set_option maxHeartbeats 0
set_option maxRecDepth 16384
namespace Blueprint.CAP.ArithmeticPilot.base_A_05_RootError_004
open Blueprint.CAP.ArithmeticPilot.base_A_05_RootRecurrence_004
def Gate : Prop := input.LogErrorGate result
theorem gate : Gate := by
  unfold Gate Blueprint.CAP.QModel.LogErrorGate
  decide +kernel
#print axioms gate
end Blueprint.CAP.ArithmeticPilot.base_A_05_RootError_004
