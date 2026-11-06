import AllS.Units.N_FI.N_kernels.RFColumns.Even049_Evaluations
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even049
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf1320.eval a
  | 0,1 => -rf1339.eval a
  | 0,2 => -rf1375.eval a
  | 0,3 => -rf1429.eval a
  | 1,0 => -rf1356.eval a
  | 1,1 => -rf1393.eval a
  | 1,2 => -rf1446.eval a
  | 2,0 => -rf1410.eval a
  | 2,1 => -rf1464.eval a
  | 2,2 => -rf1500.eval a
  | 3,0 => -rf1481.eval a
  | 3,1 => -rf1518.eval a
  | _,_ => 0

end Blueprint.Thomson.Finite.RFColumnProofs.Even049
