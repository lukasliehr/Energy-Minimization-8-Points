import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0089
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0090
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0091
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0092
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0093
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0094
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0095
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0096
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0097
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0098

namespace Blueprint.CAP.Literals.base_A_01
def block_M1_even : Block := {
  name := "M1_even"
  order := 22
  diagonalExponents := [-2, -3, -2, -3, -3, -7, -2, -6, -4, -4, -4, -5, -10, -5, -6, -9, -6, -8, -8, -10, -10, -7]
  strictLower := (chunk0089)
  factors := [(chunk0090),
    (chunk0091),
    (chunk0092),
    (chunk0093),
    (chunk0094),
    (chunk0095),
    (chunk0096),
    (chunk0097),
    (chunk0098)] }
theorem block_M1_even_shape : (block_M1_even).Shape 8 := by
  simp [Block.Shape, block_M1_even, List.length_append, chunk0089_length, chunk0090_length, chunk0091_length, chunk0092_length, chunk0093_length, chunk0094_length, chunk0095_length, chunk0096_length, chunk0097_length, chunk0098_length]
#print axioms block_M1_even_shape
end Blueprint.CAP.Literals.base_A_01
