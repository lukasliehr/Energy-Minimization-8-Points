import ThomsonNegative.Certificate.Correction.q07.Row13

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction13_6 : (centerEquation Source.r13n residual (centers13 6) 3092 28 1024 6).check=true := by decide +kernel
theorem contraction13_7 : (centerEquation Source.r13n residual (centers13 7) 3092 28 1024 7).check=true := by decide +kernel
theorem contraction13_8 : (centerEquation Source.r13n residual (centers13 8) 3092 28 1024 8).check=true := by decide +kernel
theorem contraction13_9 : (centerEquation Source.r13n residual (centers13 9) 3092 28 1024 9).check=true := by decide +kernel
theorem contraction13_10 : (centerEquation Source.r13n residual (centers13 10) 3092 28 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
