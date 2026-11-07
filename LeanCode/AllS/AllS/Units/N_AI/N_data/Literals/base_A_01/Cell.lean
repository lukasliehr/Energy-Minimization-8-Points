import AllS.Units.N_AI.N_data.Literals.base_A_01.Block_F0
import AllS.Units.N_AI.N_data.Literals.base_A_01.Block_F1
import AllS.Units.N_AI.N_data.Literals.base_A_01.Block_F2
import AllS.Units.N_AI.N_data.Literals.base_A_01.Block_F3
import AllS.Units.N_AI.N_data.Literals.base_A_01.Block_F4
import AllS.Units.N_AI.N_data.Literals.base_A_01.Block_F5
import AllS.Units.N_AI.N_data.Literals.base_A_01.Block_M0_plus
import AllS.Units.N_AI.N_data.Literals.base_A_01.Block_M0_sign
import AllS.Units.N_AI.N_data.Literals.base_A_01.Block_M0_standard
import AllS.Units.N_AI.N_data.Literals.base_A_01.Block_M1_even
import AllS.Units.N_AI.N_data.Literals.base_A_01.Block_M1_odd
import AllS.Units.N_AI.N_data.Literals.base_A_01.Block_Mdet_plus
import AllS.Units.N_AI.N_data.Literals.base_A_01.Block_Mdet_standard

namespace Blueprint.CAP.Literals.base_A_01
def value : Cell := {
  id := "base_A_01"
  degree := 12
  center := (1 / 5 : Rat)
  halfwidth := (1 / 5 : Rat)
  validationOrder := 12
  bernsteinDegree := 8
  profile := .original
  balance := .unit
  factorBits := 64
  metricBits := 64
  floorExponent := -4
  momentPivots := [0, 3, 2, 1, 0, 0]
  auxiliaryNodes := []
  rootCoefficients := [25828963179211335662156559469079587008898922291180733848624807976317948932370, 1927241089281937442171384500666790044171820957094116351976648763124444631594, -38836937292707042765165022835503050142701458434776277483731528750991235338, 95960514463046409443339075395119186413264377624526435950664433616644560, 11363720403364106322514000756761261841518022336844208877830020805077039, -206095376513693673116698962272200001619697513708363647574786346154459, -409401396197419294954510377974307643529335596377888721119805204507, 58010516835841126704209898228088231654799732016745169332583429307, -342829516877397971740713405021953244265854943581395358927328955, -16073274065282777344377170752670669494068840566861472149857995, 246571610927375539659701126753460409280585509101443866330697, 3910579461116561481197003548656434409666845727087034536321, -132175748786219954659942744806060186339737490594213907474]
  jointDepth := 0
  jointExactBlocks := []
  blocks := [block_F0, block_F1, block_F2, block_F3, block_F4, block_F5, block_M0_plus, block_M0_sign, block_M0_standard, block_M1_even, block_M1_odd, block_Mdet_plus, block_Mdet_standard]
}
theorem value_shape : value.Shape := by
  simp [Cell.Shape, value, block_F0_shape, block_F1_shape, block_F2_shape, block_F3_shape, block_F4_shape, block_F5_shape, block_M0_plus_shape, block_M0_sign_shape, block_M0_standard_shape, block_M1_even_shape, block_M1_odd_shape, block_Mdet_plus_shape, block_Mdet_standard_shape]
#print axioms value_shape
end Blueprint.CAP.Literals.base_A_01
