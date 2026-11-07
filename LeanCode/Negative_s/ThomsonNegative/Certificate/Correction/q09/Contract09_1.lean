import ThomsonNegative.Certificate.Correction.q09.Row09

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction9_6 : (centerEquation Source.r9n residual (centers9 6) 3094 42 1024 6).check=true := by decide +kernel
theorem contraction9_7 : (centerEquation Source.r9n residual (centers9 7) 3094 42 1024 7).check=true := by decide +kernel
theorem contraction9_8 : (centerEquation Source.r9n residual (centers9 8) 3094 42 1024 8).check=true := by decide +kernel
theorem contraction9_9 : (centerEquation Source.r9n residual (centers9 9) 3094 42 1024 9).check=true := by decide +kernel
theorem contraction9_10 : (centerEquation Source.r9n residual (centers9 10) 3094 42 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
