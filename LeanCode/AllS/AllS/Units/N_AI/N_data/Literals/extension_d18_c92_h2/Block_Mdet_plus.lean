import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0347
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0348
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0349
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0350
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0351
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0352
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0353
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0354
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0355
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0356
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0357
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0358

namespace Blueprint.CAP.Literals.extension_d18_c92_h2
def block_Mdet_plus : Block := {
  name := "Mdet_plus"
  order := 26
  diagonalExponents := [-11, -10, -12, -11, -10, -11, -9, -11, -11, -11, -16, -9, -12, -11, -12, -12, -13, -18, -13, -12, -15, -13, -14, -15, -17, -22]
  strictLower := (chunk0347)
  factors := [(chunk0348),
    (chunk0349),
    (chunk0350),
    (chunk0351),
    (chunk0352),
    (chunk0353),
    (chunk0354),
    (chunk0355),
    (chunk0356),
    (chunk0357),
    (chunk0358)] }
theorem block_Mdet_plus_shape : (block_Mdet_plus).Shape 10 := by
  simp [Block.Shape, block_Mdet_plus, List.length_append, chunk0347_length, chunk0348_length, chunk0349_length, chunk0350_length, chunk0351_length, chunk0352_length, chunk0353_length, chunk0354_length, chunk0355_length, chunk0356_length, chunk0357_length, chunk0358_length]
#print axioms block_Mdet_plus_shape
end Blueprint.CAP.Literals.extension_d18_c92_h2
