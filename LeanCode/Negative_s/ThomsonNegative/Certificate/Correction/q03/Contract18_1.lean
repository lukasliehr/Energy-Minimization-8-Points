import ThomsonNegative.Certificate.Correction.q03.Row18

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction18_6 : (centerEquation Source.r18n residual (centers18 6) 3116 62 1031 6).check=true := by decide +kernel
theorem contraction18_7 : (centerEquation Source.r18n residual (centers18 7) 3116 62 1031 7).check=true := by decide +kernel
theorem contraction18_8 : (centerEquation Source.r18n residual (centers18 8) 3116 62 1031 8).check=true := by decide +kernel
theorem contraction18_9 : (centerEquation Source.r18n residual (centers18 9) 3116 62 1031 9).check=true := by decide +kernel
theorem contraction18_10 : (centerEquation Source.r18n residual (centers18 10) 3116 62 1031 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
