import AllS.Units.N_AI.N_data.ScalarErrorGates
import AllS.Units.N_AI.N_data.ArithmeticPilot.finite_d14_c50_RootRecurrence_003
import AllS.Units.N_AI.N_data.ArithmeticPilot.finite_d14_c50_RootExpPoint_012
import AllS.Units.N_AI.N_data.ArithmeticPilot.finite_d14_c50_RootExpPoint_014
set_option maxHeartbeats 0
set_option maxRecDepth 16384
namespace Blueprint.CAP.ArithmeticPilot.finite_d14_c50_RootError_003
open Blueprint.CAP.ArithmeticPilot.finite_d14_c50_RootRecurrence_003
def E1 : Rat := Blueprint.CAP.ArithmeticPilot.finite_d14_c50_RootExpPoint_012.enclosure.hi
def E2 : Rat := Blueprint.CAP.ArithmeticPilot.finite_d14_c50_RootExpPoint_014.enclosure.hi
def Gate : Prop := input.ExpErrorGate result E1 E2
def PointInputs : Prop := input.variation = Blueprint.CAP.ArithmeticPilot.finite_d14_c50_RootExpPoint_012.z ∧ input.hull.hi = Blueprint.CAP.ArithmeticPilot.finite_d14_c50_RootExpPoint_014.z
theorem gate : Gate := by
  unfold Gate Blueprint.CAP.QModel.ExpErrorGate
  decide +kernel
theorem point_inputs : PointInputs := by
  unfold PointInputs
  decide +kernel
#print axioms point_inputs
#print axioms gate
end Blueprint.CAP.ArithmeticPilot.finite_d14_c50_RootError_003
