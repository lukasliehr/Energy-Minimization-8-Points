import ThomsonNegative.Certificate.Correction.q03.Row23

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction23_0 : (centerEquation Source.r23n residual (centers23 0) 3249 65 1075 0).check=true := by decide +kernel
theorem contraction23_1 : (centerEquation Source.r23n residual (centers23 1) 3249 65 1075 1).check=true := by decide +kernel
theorem contraction23_2 : (centerEquation Source.r23n residual (centers23 2) 3249 65 1075 2).check=true := by decide +kernel
theorem contraction23_3 : (centerEquation Source.r23n residual (centers23 3) 3249 65 1075 3).check=true := by decide +kernel
theorem contraction23_4 : (centerEquation Source.r23n residual (centers23 4) 3249 65 1075 4).check=true := by decide +kernel
theorem contraction23_5 : (centerEquation Source.r23n residual (centers23 5) 3249 65 1075 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
