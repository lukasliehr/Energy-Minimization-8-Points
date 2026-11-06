import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0119
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0120
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0121
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0122
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0123
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0124
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0125
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0126
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0127
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0128

namespace Blueprint.CAP.Literals.base_A_01
def block_Mdet_standard : Block := {
  name := "Mdet_standard"
  order := 4
  diagonalExponents := [-4, -2, -5, -7]
  strictLower := (chunk0119)
  factors := [(chunk0120),
    (chunk0121),
    (chunk0122),
    (chunk0123),
    (chunk0124),
    (chunk0125),
    (chunk0126),
    (chunk0127),
    (chunk0128)] }
theorem block_Mdet_standard_shape : (block_Mdet_standard).Shape 8 := by
  simp [Block.Shape, block_Mdet_standard, List.length_append, chunk0119_length, chunk0120_length, chunk0121_length, chunk0122_length, chunk0123_length, chunk0124_length, chunk0125_length, chunk0126_length, chunk0127_length, chunk0128_length]
#print axioms block_Mdet_standard_shape
end Blueprint.CAP.Literals.base_A_01
