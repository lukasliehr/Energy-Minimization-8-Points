import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0059
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0060
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0061
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0062
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0063
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0064
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0065
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0066
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0067
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0068

namespace Blueprint.CAP.Literals.base_A_01
def block_M0_plus : Block := {
  name := "M0_plus"
  order := 18
  diagonalExponents := [-2, -2, -4, -3, -3, -6, -3, -4, -5, -6, -10, -3, -7, -6, -7, -7, -10, -14]
  strictLower := (chunk0059)
  factors := [(chunk0060),
    (chunk0061),
    (chunk0062),
    (chunk0063),
    (chunk0064),
    (chunk0065),
    (chunk0066),
    (chunk0067),
    (chunk0068)] }
theorem block_M0_plus_shape : (block_M0_plus).Shape 8 := by
  simp [Block.Shape, block_M0_plus, List.length_append, chunk0059_length, chunk0060_length, chunk0061_length, chunk0062_length, chunk0063_length, chunk0064_length, chunk0065_length, chunk0066_length, chunk0067_length, chunk0068_length]
#print axioms block_M0_plus_shape
end Blueprint.CAP.Literals.base_A_01
