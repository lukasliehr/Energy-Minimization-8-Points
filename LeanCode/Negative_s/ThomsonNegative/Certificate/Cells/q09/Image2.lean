import ThomsonNegative.Certificate.Cells.q09.Basis
import ThomsonNegative.Certificate.Cells.q09.Factors

namespace ThomsonNegative.Certificate.Cells.q09
set_option maxRecDepth 8192
set_option maxHeartbeats 100000000
noncomputable def image2 : BlockImage := blockImage context basis 2 initial2
theorem image2_gate_pass : image2.ok = true := by decide +kernel
#print axioms image2_gate_pass
end ThomsonNegative.Certificate.Cells.q09
