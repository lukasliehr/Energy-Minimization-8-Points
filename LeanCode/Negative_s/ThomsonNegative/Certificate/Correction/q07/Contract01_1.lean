import ThomsonNegative.Certificate.Correction.q07.Row01

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction1_6 : (centerEquation Source.r1n residual (centers1 6) 3094 46 1024 6).check=true := by decide +kernel
theorem contraction1_7 : (centerEquation Source.r1n residual (centers1 7) 3094 46 1024 7).check=true := by decide +kernel
theorem contraction1_8 : (centerEquation Source.r1n residual (centers1 8) 3094 46 1024 8).check=true := by decide +kernel
theorem contraction1_9 : (centerEquation Source.r1n residual (centers1 9) 3094 46 1024 9).check=true := by decide +kernel
theorem contraction1_10 : (centerEquation Source.r1n residual (centers1 10) 3094 46 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
