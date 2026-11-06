import ThomsonNegative.Certificate.Correction.q03.Row40

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction40_6 : (centerEquation Source.r40n residual (centers40 6) 3095 58 1024 6).check=true := by decide +kernel
theorem contraction40_7 : (centerEquation Source.r40n residual (centers40 7) 3095 58 1024 7).check=true := by decide +kernel
theorem contraction40_8 : (centerEquation Source.r40n residual (centers40 8) 3095 58 1024 8).check=true := by decide +kernel
theorem contraction40_9 : (centerEquation Source.r40n residual (centers40 9) 3095 58 1024 9).check=true := by decide +kernel
theorem contraction40_10 : (centerEquation Source.r40n residual (centers40 10) 3095 58 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
