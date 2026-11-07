import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0359
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0360
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0361
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0362
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0363
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0364
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0365
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0366
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0367
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0368
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0369
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0370

namespace Blueprint.CAP.Literals.extension_d18_c92_h2
def block_Mdet_sign : Block := {
  name := "Mdet_sign"
  order := 9
  diagonalExponents := [-10, -11, -11, -12, -14, -13, -15, -16, -19]
  strictLower := (chunk0359)
  factors := [(chunk0360),
    (chunk0361),
    (chunk0362),
    (chunk0363),
    (chunk0364),
    (chunk0365),
    (chunk0366),
    (chunk0367),
    (chunk0368),
    (chunk0369),
    (chunk0370)] }
theorem block_Mdet_sign_shape : (block_Mdet_sign).Shape 10 := by
  simp [Block.Shape, block_Mdet_sign, List.length_append, chunk0359_length, chunk0360_length, chunk0361_length, chunk0362_length, chunk0363_length, chunk0364_length, chunk0365_length, chunk0366_length, chunk0367_length, chunk0368_length, chunk0369_length, chunk0370_length]
#print axioms block_Mdet_sign_shape
end Blueprint.CAP.Literals.extension_d18_c92_h2
