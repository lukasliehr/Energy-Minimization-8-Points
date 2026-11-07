import ThomsonNegative.Certificate.Cells.q01.Basis
import ThomsonNegative.Certificate.Cells.q01.Factors

namespace ThomsonNegative.Certificate.Cells.q01
set_option maxRecDepth 8192
set_option maxHeartbeats 100000000
noncomputable def image6 : BlockImage := blockImage context basis 6 initial6
theorem image6_gate_pass : image6.ok = true := by decide +kernel
#print axioms image6_gate_pass
end ThomsonNegative.Certificate.Cells.q01
