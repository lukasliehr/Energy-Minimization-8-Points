import ThomsonNegative.Certificate.Correction.q05.Row16

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction16_6 : (centerEquation Source.r16n residual (centers16 6) 3091 23 1024 6).check=true := by decide +kernel
theorem contraction16_7 : (centerEquation Source.r16n residual (centers16 7) 3091 23 1024 7).check=true := by decide +kernel
theorem contraction16_8 : (centerEquation Source.r16n residual (centers16 8) 3091 23 1024 8).check=true := by decide +kernel
theorem contraction16_9 : (centerEquation Source.r16n residual (centers16 9) 3091 23 1024 9).check=true := by decide +kernel
theorem contraction16_10 : (centerEquation Source.r16n residual (centers16 10) 3091 23 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
