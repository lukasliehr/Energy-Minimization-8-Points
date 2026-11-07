import ThomsonNegative.Certificate.Correction.q07.Row16

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction16_0 : (centerEquation Source.r16n residual (centers16 0) 3091 23 1024 0).check=true := by decide +kernel
theorem contraction16_1 : (centerEquation Source.r16n residual (centers16 1) 3091 23 1024 1).check=true := by decide +kernel
theorem contraction16_2 : (centerEquation Source.r16n residual (centers16 2) 3091 23 1024 2).check=true := by decide +kernel
theorem contraction16_3 : (centerEquation Source.r16n residual (centers16 3) 3091 23 1024 3).check=true := by decide +kernel
theorem contraction16_4 : (centerEquation Source.r16n residual (centers16 4) 3091 23 1024 4).check=true := by decide +kernel
theorem contraction16_5 : (centerEquation Source.r16n residual (centers16 5) 3091 23 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
