import ThomsonNegative.Certificate.Correction.q07.Row04

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction4_0 : (centerEquation Source.r4n residual (centers4 0) 3094 43 1024 0).check=true := by decide +kernel
theorem contraction4_1 : (centerEquation Source.r4n residual (centers4 1) 3094 43 1024 1).check=true := by decide +kernel
theorem contraction4_2 : (centerEquation Source.r4n residual (centers4 2) 3094 43 1024 2).check=true := by decide +kernel
theorem contraction4_3 : (centerEquation Source.r4n residual (centers4 3) 3094 43 1024 3).check=true := by decide +kernel
theorem contraction4_4 : (centerEquation Source.r4n residual (centers4 4) 3094 43 1024 4).check=true := by decide +kernel
theorem contraction4_5 : (centerEquation Source.r4n residual (centers4 5) 3094 43 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
