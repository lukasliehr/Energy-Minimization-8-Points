import ThomsonNegative.Certificate.Correction.q07.Row64

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction64_0 : (centerEquation Source.r64n residual (centers64 0) 3094 49 1024 0).check=true := by decide +kernel
theorem contraction64_1 : (centerEquation Source.r64n residual (centers64 1) 3094 49 1024 1).check=true := by decide +kernel
theorem contraction64_2 : (centerEquation Source.r64n residual (centers64 2) 3094 49 1024 2).check=true := by decide +kernel
theorem contraction64_3 : (centerEquation Source.r64n residual (centers64 3) 3094 49 1024 3).check=true := by decide +kernel
theorem contraction64_4 : (centerEquation Source.r64n residual (centers64 4) 3094 49 1024 4).check=true := by decide +kernel
theorem contraction64_5 : (centerEquation Source.r64n residual (centers64 5) 3094 49 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
