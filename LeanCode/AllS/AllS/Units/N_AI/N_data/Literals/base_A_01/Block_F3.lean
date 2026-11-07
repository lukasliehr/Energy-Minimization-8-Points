import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0030
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0031
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0032
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0033
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0034
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0035
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0036
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0037
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0038
import AllS.Units.N_AI.N_data.Literals.base_A_01.Chunk0039

namespace Blueprint.CAP.Literals.base_A_01
def block_F3 : Block := {
  name := "F3"
  order := 3
  diagonalExponents := [-4, -3, -4]
  strictLower := (chunk0030)
  factors := [(chunk0031),
    (chunk0032),
    (chunk0033),
    (chunk0034),
    (chunk0035),
    (chunk0036),
    (chunk0037),
    (chunk0038),
    (chunk0039)] }
theorem block_F3_shape : (block_F3).Shape 8 := by
  simp [Block.Shape, block_F3, List.length_append, chunk0030_length, chunk0031_length, chunk0032_length, chunk0033_length, chunk0034_length, chunk0035_length, chunk0036_length, chunk0037_length, chunk0038_length, chunk0039_length]
#print axioms block_F3_shape
end Blueprint.CAP.Literals.base_A_01
