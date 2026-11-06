import ThomsonNegative.Certificate.Correction.q01.Row63

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction63_6 : (centerEquation Source.r63n residual (centers63 6) 3095 51 1024 6).check=true := by decide +kernel
theorem contraction63_7 : (centerEquation Source.r63n residual (centers63 7) 3095 51 1024 7).check=true := by decide +kernel
theorem contraction63_8 : (centerEquation Source.r63n residual (centers63 8) 3095 51 1024 8).check=true := by decide +kernel
theorem contraction63_9 : (centerEquation Source.r63n residual (centers63 9) 3095 51 1024 9).check=true := by decide +kernel
theorem contraction63_10 : (centerEquation Source.r63n residual (centers63 10) 3095 51 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
