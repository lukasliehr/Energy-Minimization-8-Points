import ThomsonNegative.Certificate.Correction.q01.Row04

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction4_6 : (centerEquation Source.r4n residual (centers4 6) 3094 43 1024 6).check=true := by decide +kernel
theorem contraction4_7 : (centerEquation Source.r4n residual (centers4 7) 3094 43 1024 7).check=true := by decide +kernel
theorem contraction4_8 : (centerEquation Source.r4n residual (centers4 8) 3094 43 1024 8).check=true := by decide +kernel
theorem contraction4_9 : (centerEquation Source.r4n residual (centers4 9) 3094 43 1024 9).check=true := by decide +kernel
theorem contraction4_10 : (centerEquation Source.r4n residual (centers4 10) 3094 43 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
