import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0036
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0037
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0038
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0039
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0040
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0041
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0042
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0043
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0044
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0045
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0046
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0047

namespace Blueprint.CAP.Literals.extension_d18_c92_h2
def block_F3 : Block := {
  name := "F3"
  order := 6
  diagonalExponents := [-16, -12, -13, -11, -13, -14]
  strictLower := (chunk0036)
  factors := [(chunk0037),
    (chunk0038),
    (chunk0039),
    (chunk0040),
    (chunk0041),
    (chunk0042),
    (chunk0043),
    (chunk0044),
    (chunk0045),
    (chunk0046),
    (chunk0047)] }
theorem block_F3_shape : (block_F3).Shape 10 := by
  simp [Block.Shape, block_F3, List.length_append, chunk0036_length, chunk0037_length, chunk0038_length, chunk0039_length, chunk0040_length, chunk0041_length, chunk0042_length, chunk0043_length, chunk0044_length, chunk0045_length, chunk0046_length, chunk0047_length]
#print axioms block_F3_shape
end Blueprint.CAP.Literals.extension_d18_c92_h2
