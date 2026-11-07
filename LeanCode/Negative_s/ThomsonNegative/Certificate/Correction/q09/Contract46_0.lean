import ThomsonNegative.Certificate.Correction.q09.Row46

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction46_0 : (centerEquation Source.r46n residual (centers46 0) 3094 49 1024 0).check=true := by decide +kernel
theorem contraction46_1 : (centerEquation Source.r46n residual (centers46 1) 3094 49 1024 1).check=true := by decide +kernel
theorem contraction46_2 : (centerEquation Source.r46n residual (centers46 2) 3094 49 1024 2).check=true := by decide +kernel
theorem contraction46_3 : (centerEquation Source.r46n residual (centers46 3) 3094 49 1024 3).check=true := by decide +kernel
theorem contraction46_4 : (centerEquation Source.r46n residual (centers46 4) 3094 49 1024 4).check=true := by decide +kernel
theorem contraction46_5 : (centerEquation Source.r46n residual (centers46 5) 3094 49 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
