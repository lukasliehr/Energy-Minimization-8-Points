import ThomsonNegative.Certificate.Cells.q03.Basis
import ThomsonNegative.Certificate.Cells.q03.Factors

namespace ThomsonNegative.Certificate.Cells.q03
set_option maxRecDepth 8192
set_option maxHeartbeats 100000000
noncomputable def image0 : BlockImage := blockImage context basis 0 initial0
theorem image0_gate_pass : image0.ok = true := by decide +kernel
#print axioms image0_gate_pass
end ThomsonNegative.Certificate.Cells.q03
