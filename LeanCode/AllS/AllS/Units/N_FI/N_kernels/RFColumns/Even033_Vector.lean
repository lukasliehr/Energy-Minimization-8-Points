import AllS.Units.N_FI.N_kernels.RFColumns.Even033_Evaluations
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even033
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf1064.eval a
  | 0,1 => -rf1079.eval a
  | 0,2 => -rf1107.eval a
  | 0,3 => -rf1149.eval a
  | 1,0 => -rf1092.eval a
  | 1,1 => -rf1121.eval a
  | 1,2 => -rf1162.eval a
  | 2,0 => -rf1134.eval a
  | 2,1 => -rf1176.eval a
  | 2,2 => -rf1204.eval a
  | 3,0 => -rf1189.eval a
  | 3,1 => -rf1218.eval a
  | _,_ => 0

end Blueprint.Thomson.Finite.RFColumnProofs.Even033
