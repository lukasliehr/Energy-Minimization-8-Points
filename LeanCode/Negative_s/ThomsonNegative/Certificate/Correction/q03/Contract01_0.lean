import ThomsonNegative.Certificate.Correction.q03.Row01

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction1_0 : (centerEquation Source.r1n residual (centers1 0) 3094 46 1024 0).check=true := by decide +kernel
theorem contraction1_1 : (centerEquation Source.r1n residual (centers1 1) 3094 46 1024 1).check=true := by decide +kernel
theorem contraction1_2 : (centerEquation Source.r1n residual (centers1 2) 3094 46 1024 2).check=true := by decide +kernel
theorem contraction1_3 : (centerEquation Source.r1n residual (centers1 3) 3094 46 1024 3).check=true := by decide +kernel
theorem contraction1_4 : (centerEquation Source.r1n residual (centers1 4) 3094 46 1024 4).check=true := by decide +kernel
theorem contraction1_5 : (centerEquation Source.r1n residual (centers1 5) 3094 46 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
