import ThomsonNegative.Certificate.Correction.q05.Row53

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction53_0 : (centerEquation Source.r53n residual (centers53 0) 3085 6 1024 0).check=true := by decide +kernel
theorem contraction53_1 : (centerEquation Source.r53n residual (centers53 1) 3085 6 1024 1).check=true := by decide +kernel
theorem contraction53_2 : (centerEquation Source.r53n residual (centers53 2) 3085 6 1024 2).check=true := by decide +kernel
theorem contraction53_3 : (centerEquation Source.r53n residual (centers53 3) 3085 6 1024 3).check=true := by decide +kernel
theorem contraction53_4 : (centerEquation Source.r53n residual (centers53 4) 3085 6 1024 4).check=true := by decide +kernel
theorem contraction53_5 : (centerEquation Source.r53n residual (centers53 5) 3085 6 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
