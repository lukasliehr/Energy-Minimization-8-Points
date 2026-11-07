import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0020
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0021
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0022
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0023
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0024
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0025
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0026
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0027
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0028
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0029

namespace Blueprint.CAP.Literals.base_A_01
def block_F2 : Block := {
  name := "F2"
  order := 4
  diagonalExponents := [-3, -4, -3, -6]
  strictLower := (chunk0020)
  factors := [(chunk0021),
    (chunk0022),
    (chunk0023),
    (chunk0024),
    (chunk0025),
    (chunk0026),
    (chunk0027),
    (chunk0028),
    (chunk0029)] }
theorem block_F2_shape : (block_F2).Shape 8 := by
  simp [Block.Shape, block_F2, List.length_append, chunk0020_length, chunk0021_length, chunk0022_length, chunk0023_length, chunk0024_length, chunk0025_length, chunk0026_length, chunk0027_length, chunk0028_length, chunk0029_length]
#print axioms block_F2_shape
end Blueprint.CAP.Literals.base_A_01
