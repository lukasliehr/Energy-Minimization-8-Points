import ThomsonNegative.Certificate.Correction.q09.Row32

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction32_0 : (centerEquation Source.r32n residual (centers32 0) 3095 54 1024 0).check=true := by decide +kernel
theorem contraction32_1 : (centerEquation Source.r32n residual (centers32 1) 3095 54 1024 1).check=true := by decide +kernel
theorem contraction32_2 : (centerEquation Source.r32n residual (centers32 2) 3095 54 1024 2).check=true := by decide +kernel
theorem contraction32_3 : (centerEquation Source.r32n residual (centers32 3) 3095 54 1024 3).check=true := by decide +kernel
theorem contraction32_4 : (centerEquation Source.r32n residual (centers32 4) 3095 54 1024 4).check=true := by decide +kernel
theorem contraction32_5 : (centerEquation Source.r32n residual (centers32 5) 3095 54 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
