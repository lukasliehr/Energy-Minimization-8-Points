import AllS.Units.N_FI.N_kernels.RFColumns.Even059_Evaluations
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even059
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf1651.eval a
  | 0,1 => -rf1675.eval a
  | 0,2 => -rf1721.eval a
  | 0,3 => -rf1790.eval a
  | 1,0 => -rf1697.eval a
  | 1,1 => -rf1744.eval a
  | 1,2 => -rf1812.eval a
  | 2,0 => -rf1766.eval a
  | 2,1 => -rf1835.eval a
  | 2,2 => -rf1881.eval a
  | 3,0 => -rf1857.eval a
  | 3,1 => -rf1904.eval a
  | _,_ => 0

end Blueprint.Thomson.Finite.RFColumnProofs.Even059
