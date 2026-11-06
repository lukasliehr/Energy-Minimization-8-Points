import AllS.Units.N_FI.N_kernels.RFColumns.Even053_Evaluations
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even053
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf1324.eval a
  | 0,1 => -rf1343.eval a
  | 0,2 => -rf1379.eval a
  | 0,3 => -rf1433.eval a
  | 1,0 => -rf1360.eval a
  | 1,1 => -rf1397.eval a
  | 1,2 => -rf1450.eval a
  | 2,0 => -rf1414.eval a
  | 2,1 => -rf1468.eval a
  | 2,2 => -rf1504.eval a
  | 3,0 => -rf1485.eval a
  | 3,1 => -rf1522.eval a
  | _,_ => 0

end Blueprint.Thomson.Finite.RFColumnProofs.Even053
