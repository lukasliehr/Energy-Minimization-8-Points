import ThomsonNegative.Certificate.Correction.q09.Row06

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction6_0 : (centerEquation Source.r6n residual (centers6 0) 3094 45 1024 0).check=true := by decide +kernel
theorem contraction6_1 : (centerEquation Source.r6n residual (centers6 1) 3094 45 1024 1).check=true := by decide +kernel
theorem contraction6_2 : (centerEquation Source.r6n residual (centers6 2) 3094 45 1024 2).check=true := by decide +kernel
theorem contraction6_3 : (centerEquation Source.r6n residual (centers6 3) 3094 45 1024 3).check=true := by decide +kernel
theorem contraction6_4 : (centerEquation Source.r6n residual (centers6 4) 3094 45 1024 4).check=true := by decide +kernel
theorem contraction6_5 : (centerEquation Source.r6n residual (centers6 5) 3094 45 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
