import ThomsonNegative.Certificate.Correction.q01.Row03

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction3_6 : (centerEquation Source.r3n residual (centers3 6) 3094 44 1024 6).check=true := by decide +kernel
theorem contraction3_7 : (centerEquation Source.r3n residual (centers3 7) 3094 44 1024 7).check=true := by decide +kernel
theorem contraction3_8 : (centerEquation Source.r3n residual (centers3 8) 3094 44 1024 8).check=true := by decide +kernel
theorem contraction3_9 : (centerEquation Source.r3n residual (centers3 9) 3094 44 1024 9).check=true := by decide +kernel
theorem contraction3_10 : (centerEquation Source.r3n residual (centers3 10) 3094 44 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
