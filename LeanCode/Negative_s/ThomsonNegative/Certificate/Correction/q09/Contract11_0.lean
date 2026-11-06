import ThomsonNegative.Certificate.Correction.q09.Row11

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction11_0 : (centerEquation Source.r11n residual (centers11 0) 3078 1 1024 0).check=true := by decide +kernel
theorem contraction11_1 : (centerEquation Source.r11n residual (centers11 1) 3078 1 1024 1).check=true := by decide +kernel
theorem contraction11_2 : (centerEquation Source.r11n residual (centers11 2) 3078 1 1024 2).check=true := by decide +kernel
theorem contraction11_3 : (centerEquation Source.r11n residual (centers11 3) 3078 1 1024 3).check=true := by decide +kernel
theorem contraction11_4 : (centerEquation Source.r11n residual (centers11 4) 3078 1 1024 4).check=true := by decide +kernel
theorem contraction11_5 : (centerEquation Source.r11n residual (centers11 5) 3078 1 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
