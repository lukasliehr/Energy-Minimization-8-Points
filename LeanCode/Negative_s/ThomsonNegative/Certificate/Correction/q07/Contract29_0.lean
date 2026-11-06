import ThomsonNegative.Certificate.Correction.q07.Row29

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction29_0 : (centerEquation Source.r29n residual (centers29 0) 3095 55 1024 0).check=true := by decide +kernel
theorem contraction29_1 : (centerEquation Source.r29n residual (centers29 1) 3095 55 1024 1).check=true := by decide +kernel
theorem contraction29_2 : (centerEquation Source.r29n residual (centers29 2) 3095 55 1024 2).check=true := by decide +kernel
theorem contraction29_3 : (centerEquation Source.r29n residual (centers29 3) 3095 55 1024 3).check=true := by decide +kernel
theorem contraction29_4 : (centerEquation Source.r29n residual (centers29 4) 3095 55 1024 4).check=true := by decide +kernel
theorem contraction29_5 : (centerEquation Source.r29n residual (centers29 5) 3095 55 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
