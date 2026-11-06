import ThomsonNegative.Certificate.Correction.q01.Row35

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction35_6 : (centerEquation Source.r35n residual (centers35 6) 3095 55 1024 6).check=true := by decide +kernel
theorem contraction35_7 : (centerEquation Source.r35n residual (centers35 7) 3095 55 1024 7).check=true := by decide +kernel
theorem contraction35_8 : (centerEquation Source.r35n residual (centers35 8) 3095 55 1024 8).check=true := by decide +kernel
theorem contraction35_9 : (centerEquation Source.r35n residual (centers35 9) 3095 55 1024 9).check=true := by decide +kernel
theorem contraction35_10 : (centerEquation Source.r35n residual (centers35 10) 3095 55 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
