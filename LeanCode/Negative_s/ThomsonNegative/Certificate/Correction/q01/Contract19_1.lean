import ThomsonNegative.Certificate.Correction.q01.Row19

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction19_6 : (centerEquation Source.r19n residual (centers19 6) 3095 58 1024 6).check=true := by decide +kernel
theorem contraction19_7 : (centerEquation Source.r19n residual (centers19 7) 3095 58 1024 7).check=true := by decide +kernel
theorem contraction19_8 : (centerEquation Source.r19n residual (centers19 8) 3095 58 1024 8).check=true := by decide +kernel
theorem contraction19_9 : (centerEquation Source.r19n residual (centers19 9) 3095 58 1024 9).check=true := by decide +kernel
theorem contraction19_10 : (centerEquation Source.r19n residual (centers19 10) 3095 58 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
