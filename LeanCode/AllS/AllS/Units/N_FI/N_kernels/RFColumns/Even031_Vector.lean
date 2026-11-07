import AllS.Units.N_FI.N_kernels.RFColumns.Even031_Evaluations
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even031
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def vector (a : ℝ) : ParityIndex false → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf1062.eval a
  | 0,1 => -rf1077.eval a
  | 0,2 => -rf1105.eval a
  | 0,3 => -rf1147.eval a
  | 1,0 => -rf1090.eval a
  | 1,1 => -rf1119.eval a
  | 1,2 => -rf1160.eval a
  | 2,0 => -rf1132.eval a
  | 2,1 => -rf1174.eval a
  | 2,2 => -rf1202.eval a
  | 3,0 => -rf1187.eval a
  | 3,1 => -rf1216.eval a
  | _,_ => 0

end Blueprint.Thomson.Finite.RFColumnProofs.Even031
