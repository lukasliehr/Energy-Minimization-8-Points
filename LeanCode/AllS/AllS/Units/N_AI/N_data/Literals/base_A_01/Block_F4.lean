import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0040
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0041
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0042
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0043
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0044
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0045
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0046
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0047
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0048
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0049

namespace Blueprint.CAP.Literals.base_A_01
def block_F4 : Block := {
  name := "F4"
  order := 2
  diagonalExponents := [-4, -3]
  strictLower := (chunk0040)
  factors := [(chunk0041),
    (chunk0042),
    (chunk0043),
    (chunk0044),
    (chunk0045),
    (chunk0046),
    (chunk0047),
    (chunk0048),
    (chunk0049)] }
theorem block_F4_shape : (block_F4).Shape 8 := by
  simp [Block.Shape, block_F4, List.length_append, chunk0040_length, chunk0041_length, chunk0042_length, chunk0043_length, chunk0044_length, chunk0045_length, chunk0046_length, chunk0047_length, chunk0048_length, chunk0049_length]
#print axioms block_F4_shape
end Blueprint.CAP.Literals.base_A_01
