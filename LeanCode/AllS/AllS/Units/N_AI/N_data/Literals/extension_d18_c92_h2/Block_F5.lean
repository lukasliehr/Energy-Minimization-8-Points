import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0060
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0061
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0062
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0063
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0064
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0065
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0066
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0067
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0068
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0069
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0070
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0071

namespace Blueprint.CAP.Literals.extension_d18_c92_h2
def block_F5 : Block := {
  name := "F5"
  order := 4
  diagonalExponents := [-15, -15, -14, -15]
  strictLower := (chunk0060)
  factors := [(chunk0061),
    (chunk0062),
    (chunk0063),
    (chunk0064),
    (chunk0065),
    (chunk0066),
    (chunk0067),
    (chunk0068),
    (chunk0069),
    (chunk0070),
    (chunk0071)] }
theorem block_F5_shape : (block_F5).Shape 10 := by
  simp [Block.Shape, block_F5, List.length_append, chunk0060_length, chunk0061_length, chunk0062_length, chunk0063_length, chunk0064_length, chunk0065_length, chunk0066_length, chunk0067_length, chunk0068_length, chunk0069_length, chunk0070_length, chunk0071_length]
#print axioms block_F5_shape
end Blueprint.CAP.Literals.extension_d18_c92_h2
