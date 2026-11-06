import ThomsonNegative.Certificate.Correction.q07.Row51

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction51_6 : (centerEquation Source.r51n residual (centers51 6) 3085 6 1024 6).check=true := by decide +kernel
theorem contraction51_7 : (centerEquation Source.r51n residual (centers51 7) 3085 6 1024 7).check=true := by decide +kernel
theorem contraction51_8 : (centerEquation Source.r51n residual (centers51 8) 3085 6 1024 8).check=true := by decide +kernel
theorem contraction51_9 : (centerEquation Source.r51n residual (centers51 9) 3085 6 1024 9).check=true := by decide +kernel
theorem contraction51_10 : (centerEquation Source.r51n residual (centers51 10) 3085 6 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
