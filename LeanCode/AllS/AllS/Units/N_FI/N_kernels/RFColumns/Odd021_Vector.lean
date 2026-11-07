import AllS.Units.N_FI.N_kernels.RFColumns.Odd021_Evaluations
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd021
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def vector (a : ℝ) : ParityIndex true → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf1228.eval a
  | 0,1 => -rf1239.eval a
  | 0,2 => -rf1259.eval a
  | 1,0 => -rf1248.eval a
  | 1,1 => -rf1268.eval a
  | 1,2 => -rf1287.eval a
  | 2,0 => -rf1278.eval a
  | 2,1 => -rf1297.eval a
  | 3,0 => -rf1307.eval a
  | _,_ => 0

end Blueprint.Thomson.Finite.RFColumnProofs.Odd021
