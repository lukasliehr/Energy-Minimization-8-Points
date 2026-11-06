import ThomsonNegative.Certificate.CoefficientKernel
import ThomsonNegative.Compact.Target.Cells.Q05

namespace ThomsonNegative.Certificate.Cells.q05
open ThomsonNegative.Compact.Packed
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000
noncomputable def basis : List TM := basisModels Compact.Target.Cells.context Compact.Target.Cells.Q05.data.heightCheckpoint

theorem basis_gate_pass : basisGate Compact.Target.Cells.context Compact.Target.Cells.Q05.data.heightCheckpoint = true := by
  decide +kernel
#print axioms basis_gate_pass
end ThomsonNegative.Certificate.Cells.q05
