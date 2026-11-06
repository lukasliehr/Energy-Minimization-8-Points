import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0143
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0144
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0145
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0146
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0147
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0148
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0149
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0150
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0151
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0152
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0153
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0154

namespace Blueprint.CAP.Literals.extension_d18_c92_h2
def block_M0_sign : Block := {
  name := "M0_sign"
  order := 21
  diagonalExponents := [-9, -10, -9, -9, -11, -9, -8, -10, -12, -9, -10, -11, -11, -16, -10, -13, -13, -14, -15, -16, -20]
  strictLower := (chunk0143)
  factors := [(chunk0144),
    (chunk0145),
    (chunk0146),
    (chunk0147),
    (chunk0148),
    (chunk0149),
    (chunk0150),
    (chunk0151),
    (chunk0152),
    (chunk0153),
    (chunk0154)] }
theorem block_M0_sign_shape : (block_M0_sign).Shape 10 := by
  simp [Block.Shape, block_M0_sign, List.length_append, chunk0143_length, chunk0144_length, chunk0145_length, chunk0146_length, chunk0147_length, chunk0148_length, chunk0149_length, chunk0150_length, chunk0151_length, chunk0152_length, chunk0153_length, chunk0154_length]
#print axioms block_M0_sign_shape
end Blueprint.CAP.Literals.extension_d18_c92_h2
