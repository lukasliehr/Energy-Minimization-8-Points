import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0084
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0085
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0086
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0087
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0088
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0089
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0090
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0091
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0092
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0093
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0094
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0095

namespace Blueprint.CAP.Literals.extension_d18_c92_h2
def block_F7 : Block := {
  name := "F7"
  order := 2
  diagonalExponents := [-16, -16]
  strictLower := (chunk0084)
  factors := [(chunk0085),
    (chunk0086),
    (chunk0087),
    (chunk0088),
    (chunk0089),
    (chunk0090),
    (chunk0091),
    (chunk0092),
    (chunk0093),
    (chunk0094),
    (chunk0095)] }
theorem block_F7_shape : (block_F7).Shape 10 := by
  simp [Block.Shape, block_F7, List.length_append, chunk0084_length, chunk0085_length, chunk0086_length, chunk0087_length, chunk0088_length, chunk0089_length, chunk0090_length, chunk0091_length, chunk0092_length, chunk0093_length, chunk0094_length, chunk0095_length]
#print axioms block_F7_shape
end Blueprint.CAP.Literals.extension_d18_c92_h2
