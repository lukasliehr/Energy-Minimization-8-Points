import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0072
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0073
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0074
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0075
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0076
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0077
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0078
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0079
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0080
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0081
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0082
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0083

namespace Blueprint.CAP.Literals.extension_d18_c92_h2
def block_F6 : Block := {
  name := "F6"
  order := 3
  diagonalExponents := [-14, -15, -15]
  strictLower := (chunk0072)
  factors := [(chunk0073),
    (chunk0074),
    (chunk0075),
    (chunk0076),
    (chunk0077),
    (chunk0078),
    (chunk0079),
    (chunk0080),
    (chunk0081),
    (chunk0082),
    (chunk0083)] }
theorem block_F6_shape : (block_F6).Shape 10 := by
  simp [Block.Shape, block_F6, List.length_append, chunk0072_length, chunk0073_length, chunk0074_length, chunk0075_length, chunk0076_length, chunk0077_length, chunk0078_length, chunk0079_length, chunk0080_length, chunk0081_length, chunk0082_length, chunk0083_length]
#print axioms block_F6_shape
end Blueprint.CAP.Literals.extension_d18_c92_h2
