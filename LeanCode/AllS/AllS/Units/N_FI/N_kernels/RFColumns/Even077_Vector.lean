import AllS.Units.N_FI.N_kernels.RFColumns.Even077_Evaluations
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even077
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf1669.eval a
  | 0,1 => -rf1693.eval a
  | 0,2 => -rf1739.eval a
  | 0,3 => -rf1808.eval a
  | 1,0 => -rf1715.eval a
  | 1,1 => -rf1762.eval a
  | 1,2 => -rf1830.eval a
  | 2,0 => -rf1784.eval a
  | 2,1 => -rf1853.eval a
  | 2,2 => -rf1899.eval a
  | 3,0 => -rf1875.eval a
  | 3,1 => -rf1922.eval a
  | _,_ => 0

end Blueprint.Thomson.Finite.RFColumnProofs.Even077
