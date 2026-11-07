import ThomsonNegative.Certificate.Correction.q03.Row37

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction37_6 : (centerEquation Source.r37n residual (centers37 6) 3095 55 1024 6).check=true := by decide +kernel
theorem contraction37_7 : (centerEquation Source.r37n residual (centers37 7) 3095 55 1024 7).check=true := by decide +kernel
theorem contraction37_8 : (centerEquation Source.r37n residual (centers37 8) 3095 55 1024 8).check=true := by decide +kernel
theorem contraction37_9 : (centerEquation Source.r37n residual (centers37 9) 3095 55 1024 9).check=true := by decide +kernel
theorem contraction37_10 : (centerEquation Source.r37n residual (centers37 10) 3095 55 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
