import AllS.Units.N_FI.N_kernels.RFColumns.Even046_Evaluations
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even046
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf1317.eval a
  | 0,1 => -rf1336.eval a
  | 0,2 => -rf1372.eval a
  | 0,3 => -rf1426.eval a
  | 1,0 => -rf1353.eval a
  | 1,1 => -rf1390.eval a
  | 1,2 => -rf1443.eval a
  | 2,0 => -rf1407.eval a
  | 2,1 => -rf1461.eval a
  | 2,2 => -rf1497.eval a
  | 3,0 => -rf1478.eval a
  | 3,1 => -rf1515.eval a
  | _,_ => 0

end Blueprint.Thomson.Finite.RFColumnProofs.Even046
