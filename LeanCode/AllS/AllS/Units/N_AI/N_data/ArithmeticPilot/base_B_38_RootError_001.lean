import AllS.Units.N_AI.N_data.ScalarErrorGates
import AllS.Units.N_AI.N_data.ArithmeticPilot.base_B_38_RootRecurrence_001
import AllS.Units.N_AI.N_data.ArithmeticPilot.base_B_38_RootExpPoint_007
import AllS.Units.N_AI.N_data.ArithmeticPilot.base_B_38_RootExpPoint_009
set_option maxHeartbeats 0
set_option maxRecDepth 16384
namespace Blueprint.CAP.ArithmeticPilot.base_B_38_RootError_001
open Blueprint.CAP.ArithmeticPilot.base_B_38_RootRecurrence_001
def E1 : Rat := Blueprint.CAP.ArithmeticPilot.base_B_38_RootExpPoint_007.enclosure.hi
def E2 : Rat := Blueprint.CAP.ArithmeticPilot.base_B_38_RootExpPoint_009.enclosure.hi
def Gate : Prop := input.ExpErrorGate result E1 E2
def PointInputs : Prop := input.variation = Blueprint.CAP.ArithmeticPilot.base_B_38_RootExpPoint_007.z ∧ input.hull.hi = Blueprint.CAP.ArithmeticPilot.base_B_38_RootExpPoint_009.z
theorem gate : Gate := by
  unfold Gate Blueprint.CAP.QModel.ExpErrorGate
  decide +kernel
theorem point_inputs : PointInputs := by
  unfold PointInputs
  decide +kernel
#print axioms point_inputs
#print axioms gate
end Blueprint.CAP.ArithmeticPilot.base_B_38_RootError_001
