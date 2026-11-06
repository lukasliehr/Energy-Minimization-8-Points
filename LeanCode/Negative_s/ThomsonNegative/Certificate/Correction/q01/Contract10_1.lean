import ThomsonNegative.Certificate.Correction.q01.Row10

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction10_6 : (centerEquation Source.r10n residual (centers10 6) 3094 41 1024 6).check=true := by decide +kernel
theorem contraction10_7 : (centerEquation Source.r10n residual (centers10 7) 3094 41 1024 7).check=true := by decide +kernel
theorem contraction10_8 : (centerEquation Source.r10n residual (centers10 8) 3094 41 1024 8).check=true := by decide +kernel
theorem contraction10_9 : (centerEquation Source.r10n residual (centers10 9) 3094 41 1024 9).check=true := by decide +kernel
theorem contraction10_10 : (centerEquation Source.r10n residual (centers10 10) 3094 41 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
