import ThomsonNegative.Certificate.Correction.q03.Row11

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction11_6 : (centerEquation Source.r11n residual (centers11 6) 3078 1 1024 6).check=true := by decide +kernel
theorem contraction11_7 : (centerEquation Source.r11n residual (centers11 7) 3078 1 1024 7).check=true := by decide +kernel
theorem contraction11_8 : (centerEquation Source.r11n residual (centers11 8) 3078 1 1024 8).check=true := by decide +kernel
theorem contraction11_9 : (centerEquation Source.r11n residual (centers11 9) 3078 1 1024 9).check=true := by decide +kernel
theorem contraction11_10 : (centerEquation Source.r11n residual (centers11 10) 3078 1 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
