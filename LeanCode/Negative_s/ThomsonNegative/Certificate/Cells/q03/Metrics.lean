import ThomsonNegative.Certificate.Cells.q03.Factors

namespace ThomsonNegative.Certificate.Cells.q03
set_option maxRecDepth 4096
set_option maxHeartbeats 10000000
noncomputable def metricGate : Bool := inverseCheck 6 metric0 inverse0 && inverseCheck 5 metric1 inverse1 && inverseCheck 11 metric6 inverse6 && inverseCheck 11 metric7 inverse7
theorem metric_gate_pass : metricGate = true := by decide +kernel
#print axioms metric_gate_pass
end ThomsonNegative.Certificate.Cells.q03
