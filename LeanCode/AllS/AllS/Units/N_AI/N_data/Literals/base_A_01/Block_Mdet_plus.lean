import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0109
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0110
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0111
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0112
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0113
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0114
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0115
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0116
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0117
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0118

namespace Blueprint.CAP.Literals.base_A_01
def block_Mdet_plus : Block := {
  name := "Mdet_plus"
  order := 6
  diagonalExponents := [-3, -2, -6, -9, -7, -10]
  strictLower := (chunk0109)
  factors := [(chunk0110),
    (chunk0111),
    (chunk0112),
    (chunk0113),
    (chunk0114),
    (chunk0115),
    (chunk0116),
    (chunk0117),
    (chunk0118)] }
theorem block_Mdet_plus_shape : (block_Mdet_plus).Shape 8 := by
  simp [Block.Shape, block_Mdet_plus, List.length_append, chunk0109_length, chunk0110_length, chunk0111_length, chunk0112_length, chunk0113_length, chunk0114_length, chunk0115_length, chunk0116_length, chunk0117_length, chunk0118_length]
#print axioms block_Mdet_plus_shape
end Blueprint.CAP.Literals.base_A_01
