import ThomsonNegative.Certificate.Cells.q03.Basis
import ThomsonNegative.Certificate.Cells.q03.Factors

namespace ThomsonNegative.Certificate.Cells.q03
set_option maxRecDepth 8192
set_option maxHeartbeats 100000000
noncomputable def image5 : BlockImage := blockImage context basis 5 initial5
theorem image5_gate_pass : image5.ok = true := by decide +kernel
#print axioms image5_gate_pass
end ThomsonNegative.Certificate.Cells.q03
