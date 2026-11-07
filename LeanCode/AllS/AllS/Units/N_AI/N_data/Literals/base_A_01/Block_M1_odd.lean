import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0099
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0100
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0101
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0102
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0103
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0104
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0105
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0106
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0107
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0108

namespace Blueprint.CAP.Literals.base_A_01
def block_M1_odd : Block := {
  name := "M1_odd"
  order := 13
  diagonalExponents := [-4, -3, -5, -4, -5, -4, -10, -5, -8, -6, -8, -8, -9]
  strictLower := (chunk0099)
  factors := [(chunk0100),
    (chunk0101),
    (chunk0102),
    (chunk0103),
    (chunk0104),
    (chunk0105),
    (chunk0106),
    (chunk0107),
    (chunk0108)] }
theorem block_M1_odd_shape : (block_M1_odd).Shape 8 := by
  simp [Block.Shape, block_M1_odd, List.length_append, chunk0099_length, chunk0100_length, chunk0101_length, chunk0102_length, chunk0103_length, chunk0104_length, chunk0105_length, chunk0106_length, chunk0107_length, chunk0108_length]
#print axioms block_M1_odd_shape
end Blueprint.CAP.Literals.base_A_01
