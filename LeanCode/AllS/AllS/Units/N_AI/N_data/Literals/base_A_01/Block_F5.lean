import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0050
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0051
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0052
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0053
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0054
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0055
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0056
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0057
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0058

namespace Blueprint.CAP.Literals.base_A_01
def block_F5 : Block := {
  name := "F5"
  order := 1
  diagonalExponents := [-4]
  strictLower := []
  factors := [(chunk0050),
    (chunk0051),
    (chunk0052),
    (chunk0053),
    (chunk0054),
    (chunk0055),
    (chunk0056),
    (chunk0057),
    (chunk0058)] }
theorem block_F5_shape : (block_F5).Shape 8 := by
  simp [Block.Shape, block_F5, List.length_append, chunk0050_length, chunk0051_length, chunk0052_length, chunk0053_length, chunk0054_length, chunk0055_length, chunk0056_length, chunk0057_length, chunk0058_length]
#print axioms block_F5_shape
end Blueprint.CAP.Literals.base_A_01
