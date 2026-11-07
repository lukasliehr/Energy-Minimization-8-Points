import ThomsonNegative.Certificate.Correction.q09.Row40

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction40_0 : (centerEquation Source.r40n residual (centers40 0) 3095 58 1024 0).check=true := by decide +kernel
theorem contraction40_1 : (centerEquation Source.r40n residual (centers40 1) 3095 58 1024 1).check=true := by decide +kernel
theorem contraction40_2 : (centerEquation Source.r40n residual (centers40 2) 3095 58 1024 2).check=true := by decide +kernel
theorem contraction40_3 : (centerEquation Source.r40n residual (centers40 3) 3095 58 1024 3).check=true := by decide +kernel
theorem contraction40_4 : (centerEquation Source.r40n residual (centers40 4) 3095 58 1024 4).check=true := by decide +kernel
theorem contraction40_5 : (centerEquation Source.r40n residual (centers40 5) 3095 58 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
