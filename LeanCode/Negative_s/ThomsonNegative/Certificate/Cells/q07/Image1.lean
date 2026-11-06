import ThomsonNegative.Certificate.Cells.q07.Basis
import ThomsonNegative.Certificate.Cells.q07.Factors

namespace ThomsonNegative.Certificate.Cells.q07
set_option maxRecDepth 8192
set_option maxHeartbeats 100000000
noncomputable def image1 : BlockImage := blockImage context basis 1 initial1
theorem image1_gate_pass : image1.ok = true := by decide +kernel
#print axioms image1_gate_pass
end ThomsonNegative.Certificate.Cells.q07
