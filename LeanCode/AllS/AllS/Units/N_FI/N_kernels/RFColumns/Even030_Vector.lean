import AllS.Units.N_FI.N_kernels.RFColumns.Even030_Evaluations
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even030
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf1061.eval a
  | 0,1 => -rf1076.eval a
  | 0,2 => -rf1104.eval a
  | 0,3 => -rf1146.eval a
  | 1,0 => -rf1089.eval a
  | 1,1 => -rf1118.eval a
  | 1,2 => -rf1159.eval a
  | 2,0 => -rf1131.eval a
  | 2,1 => -rf1173.eval a
  | 2,2 => -rf1201.eval a
  | 3,0 => -rf1186.eval a
  | 3,1 => -rf1215.eval a
  | _,_ => 0

end Blueprint.Thomson.Finite.RFColumnProofs.Even030
