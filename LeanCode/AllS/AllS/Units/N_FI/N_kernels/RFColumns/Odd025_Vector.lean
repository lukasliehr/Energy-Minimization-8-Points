import AllS.Units.N_FI.N_kernels.RFColumns.Odd025_Evaluations
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd025
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def vector (a : ℝ) : ParityIndex true → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf1524.eval a
  | 0,1 => -rf1539.eval a
  | 0,2 => -rf1568.eval a
  | 1,0 => -rf1553.eval a
  | 1,1 => -rf1581.eval a
  | 1,2 => -rf1610.eval a
  | 2,0 => -rf1595.eval a
  | 2,1 => -rf1624.eval a
  | 3,0 => -rf1638.eval a
  | _,_ => 0

end Blueprint.Thomson.Finite.RFColumnProofs.Odd025
