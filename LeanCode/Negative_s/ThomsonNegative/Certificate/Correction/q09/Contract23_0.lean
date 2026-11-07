import ThomsonNegative.Certificate.Correction.q09.Row23

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction23_0 : (centerEquation Source.r23n residual (centers23 0) 3258 65 1078 0).check=true := by decide +kernel
theorem contraction23_1 : (centerEquation Source.r23n residual (centers23 1) 3258 65 1078 1).check=true := by decide +kernel
theorem contraction23_2 : (centerEquation Source.r23n residual (centers23 2) 3258 65 1078 2).check=true := by decide +kernel
theorem contraction23_3 : (centerEquation Source.r23n residual (centers23 3) 3258 65 1078 3).check=true := by decide +kernel
theorem contraction23_4 : (centerEquation Source.r23n residual (centers23 4) 3258 65 1078 4).check=true := by decide +kernel
theorem contraction23_5 : (centerEquation Source.r23n residual (centers23 5) 3258 65 1078 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
