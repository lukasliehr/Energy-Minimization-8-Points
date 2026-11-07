import ThomsonNegative.Certificate.Correction.q07.Row21

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction21_0 : (centerEquation Source.r21n residual (centers21 0) 3095 60 1024 0).check=true := by decide +kernel
theorem contraction21_1 : (centerEquation Source.r21n residual (centers21 1) 3095 60 1024 1).check=true := by decide +kernel
theorem contraction21_2 : (centerEquation Source.r21n residual (centers21 2) 3095 60 1024 2).check=true := by decide +kernel
theorem contraction21_3 : (centerEquation Source.r21n residual (centers21 3) 3095 60 1024 3).check=true := by decide +kernel
theorem contraction21_4 : (centerEquation Source.r21n residual (centers21 4) 3095 60 1024 4).check=true := by decide +kernel
theorem contraction21_5 : (centerEquation Source.r21n residual (centers21 5) 3095 60 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
