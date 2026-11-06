import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0096
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0097
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0098
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0099
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0100
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0101
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0102
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0103
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0104
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0105
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0106

namespace Blueprint.CAP.Literals.extension_d18_c92_h2
def block_F8 : Block := {
  name := "F8"
  order := 1
  diagonalExponents := [-17]
  strictLower := []
  factors := [(chunk0096),
    (chunk0097),
    (chunk0098),
    (chunk0099),
    (chunk0100),
    (chunk0101),
    (chunk0102),
    (chunk0103),
    (chunk0104),
    (chunk0105),
    (chunk0106)] }
theorem block_F8_shape : (block_F8).Shape 10 := by
  simp [Block.Shape, block_F8, List.length_append, chunk0096_length, chunk0097_length, chunk0098_length, chunk0099_length, chunk0100_length, chunk0101_length, chunk0102_length, chunk0103_length, chunk0104_length, chunk0105_length, chunk0106_length]
#print axioms block_F8_shape
end Blueprint.CAP.Literals.extension_d18_c92_h2
