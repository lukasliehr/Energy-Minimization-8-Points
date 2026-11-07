import ThomsonNegative.Certificate.Correction.q09.Row18

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction18_6 : (centerEquation Source.r18n residual (centers18 6) 3125 62 1034 6).check=true := by decide +kernel
theorem contraction18_7 : (centerEquation Source.r18n residual (centers18 7) 3125 62 1034 7).check=true := by decide +kernel
theorem contraction18_8 : (centerEquation Source.r18n residual (centers18 8) 3125 62 1034 8).check=true := by decide +kernel
theorem contraction18_9 : (centerEquation Source.r18n residual (centers18 9) 3125 62 1034 9).check=true := by decide +kernel
theorem contraction18_10 : (centerEquation Source.r18n residual (centers18 10) 3125 62 1034 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
