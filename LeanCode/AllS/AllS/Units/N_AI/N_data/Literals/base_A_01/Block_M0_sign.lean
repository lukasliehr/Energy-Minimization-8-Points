import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0069
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0070
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0071
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0072
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0073
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0074
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0075
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0076
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0077
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0078

namespace Blueprint.CAP.Literals.base_A_01
def block_M0_sign : Block := {
  name := "M0_sign"
  order := 5
  diagonalExponents := [-5, -6, -5, -5, -11]
  strictLower := (chunk0069)
  factors := [(chunk0070),
    (chunk0071),
    (chunk0072),
    (chunk0073),
    (chunk0074),
    (chunk0075),
    (chunk0076),
    (chunk0077),
    (chunk0078)] }
theorem block_M0_sign_shape : (block_M0_sign).Shape 8 := by
  simp [Block.Shape, block_M0_sign, List.length_append, chunk0069_length, chunk0070_length, chunk0071_length, chunk0072_length, chunk0073_length, chunk0074_length, chunk0075_length, chunk0076_length, chunk0077_length, chunk0078_length]
#print axioms block_M0_sign_shape
end Blueprint.CAP.Literals.base_A_01
