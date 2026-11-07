import ThomsonNegative.Certificate.Correction.q05.Row50

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction50_0 : (centerEquation Source.r50n residual (centers50 0) 3085 6 1024 0).check=true := by decide +kernel
theorem contraction50_1 : (centerEquation Source.r50n residual (centers50 1) 3085 6 1024 1).check=true := by decide +kernel
theorem contraction50_2 : (centerEquation Source.r50n residual (centers50 2) 3085 6 1024 2).check=true := by decide +kernel
theorem contraction50_3 : (centerEquation Source.r50n residual (centers50 3) 3085 6 1024 3).check=true := by decide +kernel
theorem contraction50_4 : (centerEquation Source.r50n residual (centers50 4) 3085 6 1024 4).check=true := by decide +kernel
theorem contraction50_5 : (centerEquation Source.r50n residual (centers50 5) 3085 6 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
