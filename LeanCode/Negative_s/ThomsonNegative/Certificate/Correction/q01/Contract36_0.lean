import ThomsonNegative.Certificate.Correction.q01.Row36

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction36_0 : (centerEquation Source.r36n residual (centers36 0) 3095 54 1024 0).check=true := by decide +kernel
theorem contraction36_1 : (centerEquation Source.r36n residual (centers36 1) 3095 54 1024 1).check=true := by decide +kernel
theorem contraction36_2 : (centerEquation Source.r36n residual (centers36 2) 3095 54 1024 2).check=true := by decide +kernel
theorem contraction36_3 : (centerEquation Source.r36n residual (centers36 3) 3095 54 1024 3).check=true := by decide +kernel
theorem contraction36_4 : (centerEquation Source.r36n residual (centers36 4) 3095 54 1024 4).check=true := by decide +kernel
theorem contraction36_5 : (centerEquation Source.r36n residual (centers36 5) 3095 54 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
