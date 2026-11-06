import ThomsonNegative.Certificate.Correction.q01.Row09

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction9_0 : (centerEquation Source.r9n residual (centers9 0) 3094 42 1024 0).check=true := by decide +kernel
theorem contraction9_1 : (centerEquation Source.r9n residual (centers9 1) 3094 42 1024 1).check=true := by decide +kernel
theorem contraction9_2 : (centerEquation Source.r9n residual (centers9 2) 3094 42 1024 2).check=true := by decide +kernel
theorem contraction9_3 : (centerEquation Source.r9n residual (centers9 3) 3094 42 1024 3).check=true := by decide +kernel
theorem contraction9_4 : (centerEquation Source.r9n residual (centers9 4) 3094 42 1024 4).check=true := by decide +kernel
theorem contraction9_5 : (centerEquation Source.r9n residual (centers9 5) 3094 42 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
