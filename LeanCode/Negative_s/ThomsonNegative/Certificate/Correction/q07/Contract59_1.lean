import ThomsonNegative.Certificate.Correction.q07.Row59

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction59_6 : (centerEquation Source.r59n residual (centers59 6) 3085 6 1024 6).check=true := by decide +kernel
theorem contraction59_7 : (centerEquation Source.r59n residual (centers59 7) 3085 6 1024 7).check=true := by decide +kernel
theorem contraction59_8 : (centerEquation Source.r59n residual (centers59 8) 3085 6 1024 8).check=true := by decide +kernel
theorem contraction59_9 : (centerEquation Source.r59n residual (centers59 9) 3085 6 1024 9).check=true := by decide +kernel
theorem contraction59_10 : (centerEquation Source.r59n residual (centers59 10) 3085 6 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
