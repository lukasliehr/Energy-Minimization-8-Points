import ThomsonNegative.Certificate.Correction.q05.Row18

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction18_6 : (centerEquation Source.r18n residual (centers18 6) 3122 62 1033 6).check=true := by decide +kernel
theorem contraction18_7 : (centerEquation Source.r18n residual (centers18 7) 3122 62 1033 7).check=true := by decide +kernel
theorem contraction18_8 : (centerEquation Source.r18n residual (centers18 8) 3122 62 1033 8).check=true := by decide +kernel
theorem contraction18_9 : (centerEquation Source.r18n residual (centers18 9) 3122 62 1033 9).check=true := by decide +kernel
theorem contraction18_10 : (centerEquation Source.r18n residual (centers18 10) 3122 62 1033 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
