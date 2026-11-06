import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0000
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0001
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0002
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0003
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0004
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0005
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0006
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0007
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0008
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0009

namespace Blueprint.CAP.Literals.base_A_01
def block_F0 : Block := {
  name := "F0"
  order := 6
  diagonalExponents := [-2, -2, -2, -5, -5, -8]
  strictLower := (chunk0000)
  factors := [(chunk0001),
    (chunk0002),
    (chunk0003),
    (chunk0004),
    (chunk0005),
    (chunk0006),
    (chunk0007),
    (chunk0008),
    (chunk0009)] }
theorem block_F0_shape : (block_F0).Shape 8 := by
  simp [Block.Shape, block_F0, List.length_append, chunk0000_length, chunk0001_length, chunk0002_length, chunk0003_length, chunk0004_length, chunk0005_length, chunk0006_length, chunk0007_length, chunk0008_length, chunk0009_length]
#print axioms block_F0_shape
end Blueprint.CAP.Literals.base_A_01
