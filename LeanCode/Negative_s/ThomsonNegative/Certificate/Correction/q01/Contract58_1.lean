import ThomsonNegative.Certificate.Correction.q01.Row58

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction58_6 : (centerEquation Source.r58n residual (centers58 6) 3085 6 1024 6).check=true := by decide +kernel
theorem contraction58_7 : (centerEquation Source.r58n residual (centers58 7) 3085 6 1024 7).check=true := by decide +kernel
theorem contraction58_8 : (centerEquation Source.r58n residual (centers58 8) 3085 6 1024 8).check=true := by decide +kernel
theorem contraction58_9 : (centerEquation Source.r58n residual (centers58 9) 3085 6 1024 9).check=true := by decide +kernel
theorem contraction58_10 : (centerEquation Source.r58n residual (centers58 10) 3085 6 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
