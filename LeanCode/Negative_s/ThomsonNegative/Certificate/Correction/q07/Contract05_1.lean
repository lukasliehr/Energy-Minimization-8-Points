import ThomsonNegative.Certificate.Correction.q07.Row05

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction5_6 : (centerEquation Source.r5n residual (centers5 6) 3094 42 1024 6).check=true := by decide +kernel
theorem contraction5_7 : (centerEquation Source.r5n residual (centers5 7) 3094 42 1024 7).check=true := by decide +kernel
theorem contraction5_8 : (centerEquation Source.r5n residual (centers5 8) 3094 42 1024 8).check=true := by decide +kernel
theorem contraction5_9 : (centerEquation Source.r5n residual (centers5 9) 3094 42 1024 9).check=true := by decide +kernel
theorem contraction5_10 : (centerEquation Source.r5n residual (centers5 10) 3094 42 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
