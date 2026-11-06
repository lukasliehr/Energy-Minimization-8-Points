import AllS.Units.N_FI.N_kernels.RFColumns.Odd044_Evaluations
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd044
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

def vector (a : ℝ) : ParityIndex true → ℝ := fun r =>
  match r.1.val,r.2.val with
  | 0,0 => -rf1928.eval a
  | 0,1 => -rf1947.eval a
  | 0,2 => -rf1984.eval a
  | 1,0 => -rf1965.eval a
  | 1,1 => -rf2002.eval a
  | 1,2 => -rf2039.eval a
  | 2,0 => -rf2020.eval a
  | 2,1 => -rf2057.eval a
  | 3,0 => -rf2075.eval a
  | _,_ => 0

end Blueprint.Thomson.Finite.RFColumnProofs.Odd044
