import AllS.Units.N_AI.N_data.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_010
import AllS.Units.N_AI.N_elementary_series.ReducedPointExpSupport
noncomputable section
namespace Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_010
open Blueprint.CAP
def Statement : Prop := enclosure.asBox.Contains (Real.exp (z:ℝ))
theorem sound : Statement := reducedPointExpSupport enclosure z 5 33 intervals gate
#print axioms sound
end Blueprint.CAP.ArithmeticPilot.extension_d18_c92_h2_RootExpPoint_010
