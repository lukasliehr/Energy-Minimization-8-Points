import ThomsonNegative.Certificate.Correction.q09.Row13

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction13_0 : (centerEquation Source.r13n residual (centers13 0) 3092 28 1024 0).check=true := by decide +kernel
theorem contraction13_1 : (centerEquation Source.r13n residual (centers13 1) 3092 28 1024 1).check=true := by decide +kernel
theorem contraction13_2 : (centerEquation Source.r13n residual (centers13 2) 3092 28 1024 2).check=true := by decide +kernel
theorem contraction13_3 : (centerEquation Source.r13n residual (centers13 3) 3092 28 1024 3).check=true := by decide +kernel
theorem contraction13_4 : (centerEquation Source.r13n residual (centers13 4) 3092 28 1024 4).check=true := by decide +kernel
theorem contraction13_5 : (centerEquation Source.r13n residual (centers13 5) 3092 28 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
