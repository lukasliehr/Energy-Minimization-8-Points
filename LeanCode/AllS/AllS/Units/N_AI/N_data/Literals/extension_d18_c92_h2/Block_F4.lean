import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0048
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0049
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0050
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0051
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0052
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0053
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0054
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0055
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0056
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0057
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0058
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0059

namespace Blueprint.CAP.Literals.extension_d18_c92_h2
def block_F4 : Block := {
  name := "F4"
  order := 5
  diagonalExponents := [-16, -14, -14, -12, -14]
  strictLower := (chunk0048)
  factors := [(chunk0049),
    (chunk0050),
    (chunk0051),
    (chunk0052),
    (chunk0053),
    (chunk0054),
    (chunk0055),
    (chunk0056),
    (chunk0057),
    (chunk0058),
    (chunk0059)] }
theorem block_F4_shape : (block_F4).Shape 10 := by
  simp [Block.Shape, block_F4, List.length_append, chunk0048_length, chunk0049_length, chunk0050_length, chunk0051_length, chunk0052_length, chunk0053_length, chunk0054_length, chunk0055_length, chunk0056_length, chunk0057_length, chunk0058_length, chunk0059_length]
#print axioms block_F4_shape
end Blueprint.CAP.Literals.extension_d18_c92_h2
