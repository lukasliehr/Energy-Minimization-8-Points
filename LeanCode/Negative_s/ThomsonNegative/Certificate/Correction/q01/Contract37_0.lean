import ThomsonNegative.Certificate.Correction.q01.Row37

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction37_0 : (centerEquation Source.r37n residual (centers37 0) 3095 55 1024 0).check=true := by decide +kernel
theorem contraction37_1 : (centerEquation Source.r37n residual (centers37 1) 3095 55 1024 1).check=true := by decide +kernel
theorem contraction37_2 : (centerEquation Source.r37n residual (centers37 2) 3095 55 1024 2).check=true := by decide +kernel
theorem contraction37_3 : (centerEquation Source.r37n residual (centers37 3) 3095 55 1024 3).check=true := by decide +kernel
theorem contraction37_4 : (centerEquation Source.r37n residual (centers37 4) 3095 55 1024 4).check=true := by decide +kernel
theorem contraction37_5 : (centerEquation Source.r37n residual (centers37 5) 3095 55 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
