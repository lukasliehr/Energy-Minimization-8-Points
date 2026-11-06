import ThomsonNegative.Certificate.Correction.q09.Row29

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction29_6 : (centerEquation Source.r29n residual (centers29 6) 3095 55 1024 6).check=true := by decide +kernel
theorem contraction29_7 : (centerEquation Source.r29n residual (centers29 7) 3095 55 1024 7).check=true := by decide +kernel
theorem contraction29_8 : (centerEquation Source.r29n residual (centers29 8) 3095 55 1024 8).check=true := by decide +kernel
theorem contraction29_9 : (centerEquation Source.r29n residual (centers29 9) 3095 55 1024 9).check=true := by decide +kernel
theorem contraction29_10 : (centerEquation Source.r29n residual (centers29 10) 3095 55 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
