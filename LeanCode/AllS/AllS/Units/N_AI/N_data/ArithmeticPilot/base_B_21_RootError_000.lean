import AllS.Units.N_AI.N_data.ScalarErrorGates
import AllS.Units.N_AI.N_data.ArithmeticPilot.base_B_21_RootRecurrence_000
import AllS.Units.N_AI.N_data.ArithmeticPilot.base_B_21_RootExpPoint_002
import AllS.Units.N_AI.N_data.ArithmeticPilot.base_B_21_RootExpPoint_004
set_option maxHeartbeats 0
set_option maxRecDepth 16384
namespace Blueprint.CAP.ArithmeticPilot.base_B_21_RootError_000
open Blueprint.CAP.ArithmeticPilot.base_B_21_RootRecurrence_000
def E1 : Rat := Blueprint.CAP.ArithmeticPilot.base_B_21_RootExpPoint_002.enclosure.hi
def E2 : Rat := Blueprint.CAP.ArithmeticPilot.base_B_21_RootExpPoint_004.enclosure.hi
def Gate : Prop := input.ExpErrorGate result E1 E2
def PointInputs : Prop := input.variation = Blueprint.CAP.ArithmeticPilot.base_B_21_RootExpPoint_002.z ∧ input.hull.hi = Blueprint.CAP.ArithmeticPilot.base_B_21_RootExpPoint_004.z
theorem gate : Gate := by
  unfold Gate Blueprint.CAP.QModel.ExpErrorGate
  decide +kernel
theorem point_inputs : PointInputs := by
  unfold PointInputs
  decide +kernel
#print axioms point_inputs
#print axioms gate
end Blueprint.CAP.ArithmeticPilot.base_B_21_RootError_000
