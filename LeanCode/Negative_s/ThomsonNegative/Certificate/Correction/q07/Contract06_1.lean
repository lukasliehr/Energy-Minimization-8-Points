import ThomsonNegative.Certificate.Correction.q07.Row06

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction6_6 : (centerEquation Source.r6n residual (centers6 6) 3094 45 1024 6).check=true := by decide +kernel
theorem contraction6_7 : (centerEquation Source.r6n residual (centers6 7) 3094 45 1024 7).check=true := by decide +kernel
theorem contraction6_8 : (centerEquation Source.r6n residual (centers6 8) 3094 45 1024 8).check=true := by decide +kernel
theorem contraction6_9 : (centerEquation Source.r6n residual (centers6 9) 3094 45 1024 9).check=true := by decide +kernel
theorem contraction6_10 : (centerEquation Source.r6n residual (centers6 10) 3094 45 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
