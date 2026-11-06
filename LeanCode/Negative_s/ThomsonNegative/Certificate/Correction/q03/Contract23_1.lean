import ThomsonNegative.Certificate.Correction.q03.Row23

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction23_6 : (centerEquation Source.r23n residual (centers23 6) 3249 65 1075 6).check=true := by decide +kernel
theorem contraction23_7 : (centerEquation Source.r23n residual (centers23 7) 3249 65 1075 7).check=true := by decide +kernel
theorem contraction23_8 : (centerEquation Source.r23n residual (centers23 8) 3249 65 1075 8).check=true := by decide +kernel
theorem contraction23_9 : (centerEquation Source.r23n residual (centers23 9) 3249 65 1075 9).check=true := by decide +kernel
theorem contraction23_10 : (centerEquation Source.r23n residual (centers23 10) 3249 65 1075 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
