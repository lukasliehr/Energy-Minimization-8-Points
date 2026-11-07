import AllS.Units.N_FI.N_kernels.RFColumns.Odd045_Evaluations
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd045
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def vector (a : ℝ) : ParityIndex true → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf1929.eval a
  | 0,1 => -rf1948.eval a
  | 0,2 => -rf1985.eval a
  | 1,0 => -rf1966.eval a
  | 1,1 => -rf2003.eval a
  | 1,2 => -rf2040.eval a
  | 2,0 => -rf2021.eval a
  | 2,1 => -rf2058.eval a
  | 3,0 => -rf2076.eval a
  | _,_ => 0

end Blueprint.Thomson.Finite.RFColumnProofs.Odd045
