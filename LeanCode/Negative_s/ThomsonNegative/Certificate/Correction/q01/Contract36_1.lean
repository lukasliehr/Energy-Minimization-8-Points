import ThomsonNegative.Certificate.Correction.q01.Row36

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction36_6 : (centerEquation Source.r36n residual (centers36 6) 3095 54 1024 6).check=true := by decide +kernel
theorem contraction36_7 : (centerEquation Source.r36n residual (centers36 7) 3095 54 1024 7).check=true := by decide +kernel
theorem contraction36_8 : (centerEquation Source.r36n residual (centers36 8) 3095 54 1024 8).check=true := by decide +kernel
theorem contraction36_9 : (centerEquation Source.r36n residual (centers36 9) 3095 54 1024 9).check=true := by decide +kernel
theorem contraction36_10 : (centerEquation Source.r36n residual (centers36 10) 3095 54 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
