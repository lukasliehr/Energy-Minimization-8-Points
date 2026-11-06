import ThomsonNegative.Certificate.Correction.q09.Row19

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction19_0 : (centerEquation Source.r19n residual (centers19 0) 3095 58 1024 0).check=true := by decide +kernel
theorem contraction19_1 : (centerEquation Source.r19n residual (centers19 1) 3095 58 1024 1).check=true := by decide +kernel
theorem contraction19_2 : (centerEquation Source.r19n residual (centers19 2) 3095 58 1024 2).check=true := by decide +kernel
theorem contraction19_3 : (centerEquation Source.r19n residual (centers19 3) 3095 58 1024 3).check=true := by decide +kernel
theorem contraction19_4 : (centerEquation Source.r19n residual (centers19 4) 3095 58 1024 4).check=true := by decide +kernel
theorem contraction19_5 : (centerEquation Source.r19n residual (centers19 5) 3095 58 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
