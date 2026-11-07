import ThomsonNegative.Certificate.Cells.q01.Basis
import ThomsonNegative.Certificate.Cells.q01.Factors

namespace ThomsonNegative.Certificate.Cells.q01
set_option maxRecDepth 8192
set_option maxHeartbeats 100000000
noncomputable def image7 : BlockImage := blockImage context basis 7 initial7
theorem image7_gate_pass : image7.ok = true := by decide +kernel
#print axioms image7_gate_pass
end ThomsonNegative.Certificate.Cells.q01
