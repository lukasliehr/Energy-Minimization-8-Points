import ThomsonNegative.Certificate.Correction.q09.Row03

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction3_0 : (centerEquation Source.r3n residual (centers3 0) 3094 44 1024 0).check=true := by decide +kernel
theorem contraction3_1 : (centerEquation Source.r3n residual (centers3 1) 3094 44 1024 1).check=true := by decide +kernel
theorem contraction3_2 : (centerEquation Source.r3n residual (centers3 2) 3094 44 1024 2).check=true := by decide +kernel
theorem contraction3_3 : (centerEquation Source.r3n residual (centers3 3) 3094 44 1024 3).check=true := by decide +kernel
theorem contraction3_4 : (centerEquation Source.r3n residual (centers3 4) 3094 44 1024 4).check=true := by decide +kernel
theorem contraction3_5 : (centerEquation Source.r3n residual (centers3 5) 3094 44 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
