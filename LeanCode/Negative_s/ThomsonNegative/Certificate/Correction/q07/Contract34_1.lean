import ThomsonNegative.Certificate.Correction.q07.Row34

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction34_6 : (centerEquation Source.r34n residual (centers34 6) 3095 51 1024 6).check=true := by decide +kernel
theorem contraction34_7 : (centerEquation Source.r34n residual (centers34 7) 3095 51 1024 7).check=true := by decide +kernel
theorem contraction34_8 : (centerEquation Source.r34n residual (centers34 8) 3095 51 1024 8).check=true := by decide +kernel
theorem contraction34_9 : (centerEquation Source.r34n residual (centers34 9) 3095 51 1024 9).check=true := by decide +kernel
theorem contraction34_10 : (centerEquation Source.r34n residual (centers34 10) 3095 51 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
