import AllS.Units.N_FI.N_kernels.RFColumns.Even040_Evaluations
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even040
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf1311.eval a
  | 0,1 => -rf1330.eval a
  | 0,2 => -rf1366.eval a
  | 0,3 => -rf1420.eval a
  | 1,0 => -rf1347.eval a
  | 1,1 => -rf1384.eval a
  | 1,2 => -rf1437.eval a
  | 2,0 => -rf1401.eval a
  | 2,1 => -rf1455.eval a
  | 2,2 => -rf1491.eval a
  | 3,0 => -rf1472.eval a
  | 3,1 => -rf1509.eval a
  | _,_ => 0

end Blueprint.Thomson.Finite.RFColumnProofs.Even040
