import AllS.Units.N_AI.N_data.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_001
import AllS.Units.N_AI.N_elementary_series.ReducedPointExpSupport
noncomputable section
namespace Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_001
open Blueprint.CAP
def Statement : Prop := enclosure.asBox.Contains (Real.exp (z:ℝ))
theorem sound : Statement := reducedPointExpSupport enclosure z 0 25 intervals gate
#print axioms sound
end Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_001
