import AllS.Units.N_FI.N_kernels.RFColumns.Even063_Evaluations
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even063
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf1655.eval a
  | 0,1 => -rf1679.eval a
  | 0,2 => -rf1725.eval a
  | 0,3 => -rf1794.eval a
  | 1,0 => -rf1701.eval a
  | 1,1 => -rf1748.eval a
  | 1,2 => -rf1816.eval a
  | 2,0 => -rf1770.eval a
  | 2,1 => -rf1839.eval a
  | 2,2 => -rf1885.eval a
  | 3,0 => -rf1861.eval a
  | 3,1 => -rf1908.eval a
  | _,_ => 0

end Blueprint.Thomson.Finite.RFColumnProofs.Even063
