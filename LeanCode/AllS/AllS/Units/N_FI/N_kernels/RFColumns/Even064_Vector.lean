import AllS.Units.N_FI.N_kernels.RFColumns.Even064_Evaluations
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even064
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf1656.eval a
  | 0,1 => -rf1680.eval a
  | 0,2 => -rf1726.eval a
  | 0,3 => -rf1795.eval a
  | 1,0 => -rf1702.eval a
  | 1,1 => -rf1749.eval a
  | 1,2 => -rf1817.eval a
  | 2,0 => -rf1771.eval a
  | 2,1 => -rf1840.eval a
  | 2,2 => -rf1886.eval a
  | 3,0 => -rf1862.eval a
  | 3,1 => -rf1909.eval a
  | _,_ => 0

end Blueprint.Thomson.Finite.RFColumnProofs.Even064
