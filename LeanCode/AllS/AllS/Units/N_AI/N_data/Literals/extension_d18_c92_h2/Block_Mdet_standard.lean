import AllS.Units.N_AI.N_data.LiteralSchema
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0371
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0372
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0373
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0374
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0375
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0376
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0377
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0378
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0379
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0380
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0381
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0382
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0383
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0384
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0385
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0386
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0387
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0388
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0389
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0390
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0391
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0392
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Chunk0393

namespace Blueprint.CAP.Literals.extension_d18_c92_h2
def block_Mdet_standard : Block := {
  name := "Mdet_standard"
  order := 32
  diagonalExponents := [-10, -8, -9, -10, -9, -10, -14, -9, -11, -11, -11, -15, -9, -13, -11, -13, -14, -16, -18, -11, -10, -10, -13, -12, -11, -12, -14, -12, -13, -13, -15, -18]
  strictLower := (chunk0371)
  factors := [(chunk0372 ++ chunk0373),
    (chunk0374 ++ chunk0375),
    (chunk0376 ++ chunk0377),
    (chunk0378 ++ chunk0379),
    (chunk0380 ++ chunk0381),
    (chunk0382 ++ chunk0383),
    (chunk0384 ++ chunk0385),
    (chunk0386 ++ chunk0387),
    (chunk0388 ++ chunk0389),
    (chunk0390 ++ chunk0391),
    (chunk0392 ++ chunk0393)] }
theorem block_Mdet_standard_shape : (block_Mdet_standard).Shape 10 := by
  simp [Block.Shape, block_Mdet_standard, List.length_append, chunk0371_length, chunk0372_length, chunk0373_length, chunk0374_length, chunk0375_length, chunk0376_length, chunk0377_length, chunk0378_length, chunk0379_length, chunk0380_length, chunk0381_length, chunk0382_length, chunk0383_length, chunk0384_length, chunk0385_length, chunk0386_length, chunk0387_length, chunk0388_length, chunk0389_length, chunk0390_length, chunk0391_length, chunk0392_length, chunk0393_length]
#print axioms block_Mdet_standard_shape
end Blueprint.CAP.Literals.extension_d18_c92_h2
