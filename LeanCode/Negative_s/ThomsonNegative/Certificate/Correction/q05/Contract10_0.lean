import ThomsonNegative.Certificate.Correction.q05.Row10

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction10_0 : (centerEquation Source.r10n residual (centers10 0) 3094 41 1024 0).check=true := by decide +kernel
theorem contraction10_1 : (centerEquation Source.r10n residual (centers10 1) 3094 41 1024 1).check=true := by decide +kernel
theorem contraction10_2 : (centerEquation Source.r10n residual (centers10 2) 3094 41 1024 2).check=true := by decide +kernel
theorem contraction10_3 : (centerEquation Source.r10n residual (centers10 3) 3094 41 1024 3).check=true := by decide +kernel
theorem contraction10_4 : (centerEquation Source.r10n residual (centers10 4) 3094 41 1024 4).check=true := by decide +kernel
theorem contraction10_5 : (centerEquation Source.r10n residual (centers10 5) 3094 41 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
