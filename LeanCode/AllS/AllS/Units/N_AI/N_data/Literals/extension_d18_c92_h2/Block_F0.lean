import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0000
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0001
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0002
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0003
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0004
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0005
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0006
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0007
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0008
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0009
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0010
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0011

namespace Blueprint.CAP.Literals.extension_d18_c92_h2
def block_F0 : Block := {
  name := "F0"
  order := 9
  diagonalExponents := [-15, -13, -12, -12, -12, -12, -12, -14, -16]
  strictLower := (chunk0000)
  factors := [(chunk0001),
    (chunk0002),
    (chunk0003),
    (chunk0004),
    (chunk0005),
    (chunk0006),
    (chunk0007),
    (chunk0008),
    (chunk0009),
    (chunk0010),
    (chunk0011)] }
theorem block_F0_shape : (block_F0).Shape 10 := by
  simp [Block.Shape, block_F0, List.length_append, chunk0000_length, chunk0001_length, chunk0002_length, chunk0003_length, chunk0004_length, chunk0005_length, chunk0006_length, chunk0007_length, chunk0008_length, chunk0009_length, chunk0010_length, chunk0011_length]
#print axioms block_F0_shape
end Blueprint.CAP.Literals.extension_d18_c92_h2
