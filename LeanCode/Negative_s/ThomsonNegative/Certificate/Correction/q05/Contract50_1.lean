import ThomsonNegative.Certificate.Correction.q05.Row50

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction50_6 : (centerEquation Source.r50n residual (centers50 6) 3085 6 1024 6).check=true := by decide +kernel
theorem contraction50_7 : (centerEquation Source.r50n residual (centers50 7) 3085 6 1024 7).check=true := by decide +kernel
theorem contraction50_8 : (centerEquation Source.r50n residual (centers50 8) 3085 6 1024 8).check=true := by decide +kernel
theorem contraction50_9 : (centerEquation Source.r50n residual (centers50 9) 3085 6 1024 9).check=true := by decide +kernel
theorem contraction50_10 : (centerEquation Source.r50n residual (centers50 10) 3085 6 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
