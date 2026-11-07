import ThomsonNegative.Certificate.Correction.q01.Row65

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction65_6 : (centerEquation Source.r65n residual (centers65 6) 3085 6 1024 6).check=true := by decide +kernel
theorem contraction65_7 : (centerEquation Source.r65n residual (centers65 7) 3085 6 1024 7).check=true := by decide +kernel
theorem contraction65_8 : (centerEquation Source.r65n residual (centers65 8) 3085 6 1024 8).check=true := by decide +kernel
theorem contraction65_9 : (centerEquation Source.r65n residual (centers65 9) 3085 6 1024 9).check=true := by decide +kernel
theorem contraction65_10 : (centerEquation Source.r65n residual (centers65 10) 3085 6 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
