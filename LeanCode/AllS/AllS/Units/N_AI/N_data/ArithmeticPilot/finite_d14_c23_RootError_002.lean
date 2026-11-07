import AllS.Units.N_AI.N_data.ScalarErrorGates
import AllS.Units.N_AI.N_data.ArithmeticPilot.finite_d14_c23_RootRecurrence_002
set_option maxHeartbeats 0
set_option maxRecDepth 16384
namespace Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootError_002
open Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootRecurrence_002
def Gate : Prop := input.LogErrorGate result
theorem gate : Gate := by
  unfold Gate Blueprint.CAP.QModel.LogErrorGate
  decide +kernel
#print axioms gate
end Blueprint.CAP.ArithmeticPilot.finite_d14_c23_RootError_002
