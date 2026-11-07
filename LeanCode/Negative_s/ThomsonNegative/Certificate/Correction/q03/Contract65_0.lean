import ThomsonNegative.Certificate.Correction.q03.Row65

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction65_0 : (centerEquation Source.r65n residual (centers65 0) 3085 6 1024 0).check=true := by decide +kernel
theorem contraction65_1 : (centerEquation Source.r65n residual (centers65 1) 3085 6 1024 1).check=true := by decide +kernel
theorem contraction65_2 : (centerEquation Source.r65n residual (centers65 2) 3085 6 1024 2).check=true := by decide +kernel
theorem contraction65_3 : (centerEquation Source.r65n residual (centers65 3) 3085 6 1024 3).check=true := by decide +kernel
theorem contraction65_4 : (centerEquation Source.r65n residual (centers65 4) 3085 6 1024 4).check=true := by decide +kernel
theorem contraction65_5 : (centerEquation Source.r65n residual (centers65 5) 3085 6 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
