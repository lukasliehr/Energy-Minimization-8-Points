import AllS.Units.N_FI.N_kernels.RFColumns.Even022_Evaluations
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even022
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf1053.eval a
  | 0,1 => -rf1068.eval a
  | 0,2 => -rf1096.eval a
  | 0,3 => -rf1138.eval a
  | 1,0 => -rf1081.eval a
  | 1,1 => -rf1110.eval a
  | 1,2 => -rf1151.eval a
  | 2,0 => -rf1123.eval a
  | 2,1 => -rf1165.eval a
  | 2,2 => -rf1193.eval a
  | 3,0 => -rf1178.eval a
  | 3,1 => -rf1207.eval a
  | _,_ => 0

end Blueprint.Thomson.Finite.RFColumnProofs.Even022
