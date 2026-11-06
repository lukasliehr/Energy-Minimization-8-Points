import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0024
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0025
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0026
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0027
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0028
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0029
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0030
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0031
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0032
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0033
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0034
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0035

namespace Blueprint.CAP.Literals.extension_d18_c92_h2
def block_F2 : Block := {
  name := "F2"
  order := 7
  diagonalExponents := [-15, -12, -12, -13, -10, -13, -15]
  strictLower := (chunk0024)
  factors := [(chunk0025),
    (chunk0026),
    (chunk0027),
    (chunk0028),
    (chunk0029),
    (chunk0030),
    (chunk0031),
    (chunk0032),
    (chunk0033),
    (chunk0034),
    (chunk0035)] }
theorem block_F2_shape : (block_F2).Shape 10 := by
  simp [Block.Shape, block_F2, List.length_append, chunk0024_length, chunk0025_length, chunk0026_length, chunk0027_length, chunk0028_length, chunk0029_length, chunk0030_length, chunk0031_length, chunk0032_length, chunk0033_length, chunk0034_length, chunk0035_length]
#print axioms block_F2_shape
end Blueprint.CAP.Literals.extension_d18_c92_h2
