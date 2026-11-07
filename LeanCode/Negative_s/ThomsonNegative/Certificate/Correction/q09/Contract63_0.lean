import ThomsonNegative.Certificate.Correction.q09.Row63

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction63_0 : (centerEquation Source.r63n residual (centers63 0) 3095 51 1024 0).check=true := by decide +kernel
theorem contraction63_1 : (centerEquation Source.r63n residual (centers63 1) 3095 51 1024 1).check=true := by decide +kernel
theorem contraction63_2 : (centerEquation Source.r63n residual (centers63 2) 3095 51 1024 2).check=true := by decide +kernel
theorem contraction63_3 : (centerEquation Source.r63n residual (centers63 3) 3095 51 1024 3).check=true := by decide +kernel
theorem contraction63_4 : (centerEquation Source.r63n residual (centers63 4) 3095 51 1024 4).check=true := by decide +kernel
theorem contraction63_5 : (centerEquation Source.r63n residual (centers63 5) 3095 51 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
