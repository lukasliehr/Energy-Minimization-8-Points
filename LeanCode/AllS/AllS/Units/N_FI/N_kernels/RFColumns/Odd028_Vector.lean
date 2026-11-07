import AllS.Units.N_FI.N_kernels.RFColumns.Odd028_Evaluations
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd028
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def vector (a : ℝ) : ParityIndex true → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf1527.eval a
  | 0,1 => -rf1542.eval a
  | 0,2 => -rf1571.eval a
  | 1,0 => -rf1556.eval a
  | 1,1 => -rf1584.eval a
  | 1,2 => -rf1613.eval a
  | 2,0 => -rf1598.eval a
  | 2,1 => -rf1627.eval a
  | 3,0 => -rf1641.eval a
  | _,_ => 0

end Blueprint.Thomson.Finite.RFColumnProofs.Odd028
