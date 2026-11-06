import ThomsonNegative.Certificate.Correction.q07.Row05

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction5_0 : (centerEquation Source.r5n residual (centers5 0) 3094 42 1024 0).check=true := by decide +kernel
theorem contraction5_1 : (centerEquation Source.r5n residual (centers5 1) 3094 42 1024 1).check=true := by decide +kernel
theorem contraction5_2 : (centerEquation Source.r5n residual (centers5 2) 3094 42 1024 2).check=true := by decide +kernel
theorem contraction5_3 : (centerEquation Source.r5n residual (centers5 3) 3094 42 1024 3).check=true := by decide +kernel
theorem contraction5_4 : (centerEquation Source.r5n residual (centers5 4) 3094 42 1024 4).check=true := by decide +kernel
theorem contraction5_5 : (centerEquation Source.r5n residual (centers5 5) 3094 42 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
