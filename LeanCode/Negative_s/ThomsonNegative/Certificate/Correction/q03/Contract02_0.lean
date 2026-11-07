import ThomsonNegative.Certificate.Correction.q03.Row02

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction2_0 : (centerEquation Source.r2n residual (centers2 0) 3094 45 1024 0).check=true := by decide +kernel
theorem contraction2_1 : (centerEquation Source.r2n residual (centers2 1) 3094 45 1024 1).check=true := by decide +kernel
theorem contraction2_2 : (centerEquation Source.r2n residual (centers2 2) 3094 45 1024 2).check=true := by decide +kernel
theorem contraction2_3 : (centerEquation Source.r2n residual (centers2 3) 3094 45 1024 3).check=true := by decide +kernel
theorem contraction2_4 : (centerEquation Source.r2n residual (centers2 4) 3094 45 1024 4).check=true := by decide +kernel
theorem contraction2_5 : (centerEquation Source.r2n residual (centers2 5) 3094 45 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
