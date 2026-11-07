import ThomsonNegative.Certificate.Correction.q09.Row48

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction48_6 : (centerEquation Source.r48n residual (centers48 6) 3085 6 1024 6).check=true := by decide +kernel
theorem contraction48_7 : (centerEquation Source.r48n residual (centers48 7) 3085 6 1024 7).check=true := by decide +kernel
theorem contraction48_8 : (centerEquation Source.r48n residual (centers48 8) 3085 6 1024 8).check=true := by decide +kernel
theorem contraction48_9 : (centerEquation Source.r48n residual (centers48 9) 3085 6 1024 9).check=true := by decide +kernel
theorem contraction48_10 : (centerEquation Source.r48n residual (centers48 10) 3085 6 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
