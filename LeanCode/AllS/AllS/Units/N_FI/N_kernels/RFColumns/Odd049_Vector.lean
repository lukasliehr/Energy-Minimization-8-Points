import AllS.Units.N_FI.N_kernels.RFColumns.Odd049_Evaluations
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd049
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def vector (a : ℝ) : ParityIndex true → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf1933.eval a
  | 0,1 => -rf1952.eval a
  | 0,2 => -rf1989.eval a
  | 1,0 => -rf1970.eval a
  | 1,1 => -rf2007.eval a
  | 1,2 => -rf2044.eval a
  | 2,0 => -rf2025.eval a
  | 2,1 => -rf2062.eval a
  | 3,0 => -rf2044.eval a
  | _,_ => 0

end Blueprint.Thomson.Finite.RFColumnProofs.Odd049
