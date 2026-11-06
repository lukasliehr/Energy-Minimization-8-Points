import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0012
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0013
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0014
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0015
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0016
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0017
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0018
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0019
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0020
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0021
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0022
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0023

namespace Blueprint.CAP.Literals.extension_d18_c92_h2
def block_F1 : Block := {
  name := "F1"
  order := 8
  diagonalExponents := [-14, -12, -10, -12, -8, -12, -14, -15]
  strictLower := (chunk0012)
  factors := [(chunk0013),
    (chunk0014),
    (chunk0015),
    (chunk0016),
    (chunk0017),
    (chunk0018),
    (chunk0019),
    (chunk0020),
    (chunk0021),
    (chunk0022),
    (chunk0023)] }
theorem block_F1_shape : (block_F1).Shape 10 := by
  simp [Block.Shape, block_F1, List.length_append, chunk0012_length, chunk0013_length, chunk0014_length, chunk0015_length, chunk0016_length, chunk0017_length, chunk0018_length, chunk0019_length, chunk0020_length, chunk0021_length, chunk0022_length, chunk0023_length]
#print axioms block_F1_shape
end Blueprint.CAP.Literals.extension_d18_c92_h2
