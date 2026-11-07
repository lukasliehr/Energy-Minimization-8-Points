import AllS.Units.N_AI.N_data.ScalarErrorGates
import AllS.Units.N_AI.N_data.ArithmeticPilot.extension_d18_c92_h2_RootRecurrence_002
set_option maxHeartbeats 0
set_option maxRecDepth 16384
namespace Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootError_002
open Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootRecurrence_002
def Gate : Prop := input.LogErrorGate result
theorem gate : Gate := by
  unfold Gate Blueprint.CAP.QModel.LogErrorGate
  decide +kernel
#print axioms gate
end Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootError_002
