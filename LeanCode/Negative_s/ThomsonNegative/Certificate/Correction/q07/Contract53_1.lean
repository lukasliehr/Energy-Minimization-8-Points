import ThomsonNegative.Certificate.Correction.q07.Row53

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction53_6 : (centerEquation Source.r53n residual (centers53 6) 3085 6 1024 6).check=true := by decide +kernel
theorem contraction53_7 : (centerEquation Source.r53n residual (centers53 7) 3085 6 1024 7).check=true := by decide +kernel
theorem contraction53_8 : (centerEquation Source.r53n residual (centers53 8) 3085 6 1024 8).check=true := by decide +kernel
theorem contraction53_9 : (centerEquation Source.r53n residual (centers53 9) 3085 6 1024 9).check=true := by decide +kernel
theorem contraction53_10 : (centerEquation Source.r53n residual (centers53 10) 3085 6 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
