import ThomsonNegative.Certificate.Correction.q07.Row42

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction42_6 : (centerEquation Source.r42n residual (centers42 6) 3095 51 1024 6).check=true := by decide +kernel
theorem contraction42_7 : (centerEquation Source.r42n residual (centers42 7) 3095 51 1024 7).check=true := by decide +kernel
theorem contraction42_8 : (centerEquation Source.r42n residual (centers42 8) 3095 51 1024 8).check=true := by decide +kernel
theorem contraction42_9 : (centerEquation Source.r42n residual (centers42 9) 3095 51 1024 9).check=true := by decide +kernel
theorem contraction42_10 : (centerEquation Source.r42n residual (centers42 10) 3095 51 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
