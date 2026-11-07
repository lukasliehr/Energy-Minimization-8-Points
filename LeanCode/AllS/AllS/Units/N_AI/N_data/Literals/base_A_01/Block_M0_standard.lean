import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0079
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0080
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0081
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0082
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0083
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0084
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0085
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0086
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0087
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0088

namespace Blueprint.CAP.Literals.base_A_01
def block_M0_standard : Block := {
  name := "M0_standard"
  order := 20
  diagonalExponents := [-2, -1, -3, -3, -3, -4, -8, -2, -4, -4, -6, -10, -4, -4, -6, -7, -7, -5, -9, -10]
  strictLower := (chunk0079)
  factors := [(chunk0080),
    (chunk0081),
    (chunk0082),
    (chunk0083),
    (chunk0084),
    (chunk0085),
    (chunk0086),
    (chunk0087),
    (chunk0088)] }
theorem block_M0_standard_shape : (block_M0_standard).Shape 8 := by
  simp [Block.Shape, block_M0_standard, List.length_append, chunk0079_length, chunk0080_length, chunk0081_length, chunk0082_length, chunk0083_length, chunk0084_length, chunk0085_length, chunk0086_length, chunk0087_length, chunk0088_length]
#print axioms block_M0_standard_shape
end Blueprint.CAP.Literals.base_A_01
