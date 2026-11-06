import AllS.Units.N_AI.N_data.RationalBernstein
import Mathlib.Data.Fin.VecNotation
import AllS.Units.N_AI.N_data.Literals.base_A_01.Cell
set_option maxHeartbeats 0
set_option maxRecDepth 8192
namespace Blueprint.CAP.ArithmeticPilot.RootControlsAll_base_A_01
attribute [local instance] Fintype.decidableForallFintype
def center : Rat := (1/5 : Rat)
def halfwidth : Rat := (1/5 : Rat)
def z : Fin 13 → Int := ![25828963179211335662156559469079587008898922291180733848624807976317948932370, 1927241089281937442171384500666790044171820957094116351976648763124444631594, -38836937292707042765165022835503050142701458434776277483731528750991235338, 95960514463046409443339075395119186413264377624526435950664433616644560, 11363720403364106322514000756761261841518022336844208877830020805077039, -206095376513693673116698962272200001619697513708363647574786346154459, -409401396197419294954510377974307643529335596377888721119805204507, 58010516835841126704209898228088231654799732016745169332583429307, -342829516877397971740713405021953244265854943581395358927328955, -16073274065282777344377170752670669494068840566861472149857995, 246571610927375539659701126753460409280585509101443866330697, 3910579461116561481197003548656434409666845727087034536321, -132175748786219954659942744806060186339737490594213907474]
def invariantUpper : Rat := (45495752179962794690739693645427246015/85070591730234615865843651857942052864 : Rat)
def ParameterGates : Prop := 0 < halfwidth ∧ 0 ≤ center-halfwidth ∧ center+halfwidth ≤ 97
def ControlGates : Prop := ∀ i : Fin 13, 0 ≤ Blueprint.CAP.rationalRootControls z i ∧ Blueprint.CAP.rationalRootControls z i ≤ invariantUpper
theorem parameter_gates : ParameterGates := by
  unfold ParameterGates
  decide +kernel
theorem control_gates : ControlGates := by
  unfold ControlGates
  decide +kernel
theorem source_inputs : List.ofFn z = Blueprint.CAP.Literals.base_A_01.value.rootCoefficients ∧ center = Blueprint.CAP.Literals.base_A_01.value.center ∧ halfwidth = Blueprint.CAP.Literals.base_A_01.value.halfwidth := ⟨rfl,rfl,rfl⟩
#print axioms source_inputs
#print axioms parameter_gates
#print axioms control_gates
end Blueprint.CAP.ArithmeticPilot.RootControlsAll_base_A_01
