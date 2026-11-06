import ThomsonNegative.Certificate.Cells.q09.Basis
import ThomsonNegative.Certificate.Cells.q09.Factors

namespace ThomsonNegative.Certificate.Cells.q09
set_option maxRecDepth 8192
set_option maxHeartbeats 100000000
noncomputable def image4 : BlockImage := blockImage context basis 4 initial4
theorem image4_gate_pass : image4.ok = true := by decide +kernel
#print axioms image4_gate_pass
end ThomsonNegative.Certificate.Cells.q09
