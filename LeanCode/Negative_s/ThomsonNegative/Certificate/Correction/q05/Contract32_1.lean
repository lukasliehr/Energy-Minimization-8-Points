import ThomsonNegative.Certificate.Correction.q05.Row32

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction32_6 : (centerEquation Source.r32n residual (centers32 6) 3095 54 1024 6).check=true := by decide +kernel
theorem contraction32_7 : (centerEquation Source.r32n residual (centers32 7) 3095 54 1024 7).check=true := by decide +kernel
theorem contraction32_8 : (centerEquation Source.r32n residual (centers32 8) 3095 54 1024 8).check=true := by decide +kernel
theorem contraction32_9 : (centerEquation Source.r32n residual (centers32 9) 3095 54 1024 9).check=true := by decide +kernel
theorem contraction32_10 : (centerEquation Source.r32n residual (centers32 10) 3095 54 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
