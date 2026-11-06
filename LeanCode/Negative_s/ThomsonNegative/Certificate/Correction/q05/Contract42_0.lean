import ThomsonNegative.Certificate.Correction.q05.Row42

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction42_0 : (centerEquation Source.r42n residual (centers42 0) 3095 51 1024 0).check=true := by decide +kernel
theorem contraction42_1 : (centerEquation Source.r42n residual (centers42 1) 3095 51 1024 1).check=true := by decide +kernel
theorem contraction42_2 : (centerEquation Source.r42n residual (centers42 2) 3095 51 1024 2).check=true := by decide +kernel
theorem contraction42_3 : (centerEquation Source.r42n residual (centers42 3) 3095 51 1024 3).check=true := by decide +kernel
theorem contraction42_4 : (centerEquation Source.r42n residual (centers42 4) 3095 51 1024 4).check=true := by decide +kernel
theorem contraction42_5 : (centerEquation Source.r42n residual (centers42 5) 3095 51 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
