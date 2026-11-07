import ThomsonNegative.Certificate.Correction.q03.Row51

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction51_0 : (centerEquation Source.r51n residual (centers51 0) 3085 6 1024 0).check=true := by decide +kernel
theorem contraction51_1 : (centerEquation Source.r51n residual (centers51 1) 3085 6 1024 1).check=true := by decide +kernel
theorem contraction51_2 : (centerEquation Source.r51n residual (centers51 2) 3085 6 1024 2).check=true := by decide +kernel
theorem contraction51_3 : (centerEquation Source.r51n residual (centers51 3) 3085 6 1024 3).check=true := by decide +kernel
theorem contraction51_4 : (centerEquation Source.r51n residual (centers51 4) 3085 6 1024 4).check=true := by decide +kernel
theorem contraction51_5 : (centerEquation Source.r51n residual (centers51 5) 3085 6 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
