import AllS.Units.N_FI.N_kernels.RFColumns.Even029_Evaluations
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even029
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf1060.eval a
  | 0,1 => -rf1075.eval a
  | 0,2 => -rf1103.eval a
  | 0,3 => -rf1145.eval a
  | 1,0 => -rf1088.eval a
  | 1,1 => -rf1117.eval a
  | 1,2 => -rf1158.eval a
  | 2,0 => -rf1130.eval a
  | 2,1 => -rf1172.eval a
  | 2,2 => -rf1200.eval a
  | 3,0 => -rf1185.eval a
  | 3,1 => -rf1214.eval a
  | _,_ => 0

end Blueprint.Thomson.Finite.RFColumnProofs.Even029
