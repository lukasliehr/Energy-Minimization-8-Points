import ThomsonNegative.Certificate.Correction.q03.Row34

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction34_0 : (centerEquation Source.r34n residual (centers34 0) 3095 51 1024 0).check=true := by decide +kernel
theorem contraction34_1 : (centerEquation Source.r34n residual (centers34 1) 3095 51 1024 1).check=true := by decide +kernel
theorem contraction34_2 : (centerEquation Source.r34n residual (centers34 2) 3095 51 1024 2).check=true := by decide +kernel
theorem contraction34_3 : (centerEquation Source.r34n residual (centers34 3) 3095 51 1024 3).check=true := by decide +kernel
theorem contraction34_4 : (centerEquation Source.r34n residual (centers34 4) 3095 51 1024 4).check=true := by decide +kernel
theorem contraction34_5 : (centerEquation Source.r34n residual (centers34 5) 3095 51 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
