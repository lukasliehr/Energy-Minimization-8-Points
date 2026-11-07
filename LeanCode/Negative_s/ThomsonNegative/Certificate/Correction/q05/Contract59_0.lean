import ThomsonNegative.Certificate.Correction.q05.Row59

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction59_0 : (centerEquation Source.r59n residual (centers59 0) 3085 6 1024 0).check=true := by decide +kernel
theorem contraction59_1 : (centerEquation Source.r59n residual (centers59 1) 3085 6 1024 1).check=true := by decide +kernel
theorem contraction59_2 : (centerEquation Source.r59n residual (centers59 2) 3085 6 1024 2).check=true := by decide +kernel
theorem contraction59_3 : (centerEquation Source.r59n residual (centers59 3) 3085 6 1024 3).check=true := by decide +kernel
theorem contraction59_4 : (centerEquation Source.r59n residual (centers59 4) 3085 6 1024 4).check=true := by decide +kernel
theorem contraction59_5 : (centerEquation Source.r59n residual (centers59 5) 3085 6 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
