import ThomsonNegative.Certificate.Cells.q07.Basis
import ThomsonNegative.Certificate.Cells.q07.Factors

namespace ThomsonNegative.Certificate.Cells.q07
set_option maxRecDepth 8192
set_option maxHeartbeats 100000000
noncomputable def image3 : BlockImage := blockImage context basis 3 initial3
theorem image3_gate_pass : image3.ok = true := by decide +kernel
#print axioms image3_gate_pass
end ThomsonNegative.Certificate.Cells.q07
