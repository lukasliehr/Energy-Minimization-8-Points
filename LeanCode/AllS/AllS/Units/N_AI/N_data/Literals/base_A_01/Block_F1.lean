import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0010
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0011
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0012
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0013
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0014
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0015
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0016
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0017
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0018
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0019

namespace Blueprint.CAP.Literals.base_A_01
def block_F1 : Block := {
  name := "F1"
  order := 5
  diagonalExponents := [-2, -2, -2, -3, -8]
  strictLower := (chunk0010)
  factors := [(chunk0011),
    (chunk0012),
    (chunk0013),
    (chunk0014),
    (chunk0015),
    (chunk0016),
    (chunk0017),
    (chunk0018),
    (chunk0019)] }
theorem block_F1_shape : (block_F1).Shape 8 := by
  simp [Block.Shape, block_F1, List.length_append, chunk0010_length, chunk0011_length, chunk0012_length, chunk0013_length, chunk0014_length, chunk0015_length, chunk0016_length, chunk0017_length, chunk0018_length, chunk0019_length]
#print axioms block_F1_shape
end Blueprint.CAP.Literals.base_A_01
