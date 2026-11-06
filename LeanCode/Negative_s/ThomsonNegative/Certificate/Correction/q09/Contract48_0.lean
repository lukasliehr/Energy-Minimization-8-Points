import ThomsonNegative.Certificate.Correction.q09.Row48

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction48_0 : (centerEquation Source.r48n residual (centers48 0) 3085 6 1024 0).check=true := by decide +kernel
theorem contraction48_1 : (centerEquation Source.r48n residual (centers48 1) 3085 6 1024 1).check=true := by decide +kernel
theorem contraction48_2 : (centerEquation Source.r48n residual (centers48 2) 3085 6 1024 2).check=true := by decide +kernel
theorem contraction48_3 : (centerEquation Source.r48n residual (centers48 3) 3085 6 1024 3).check=true := by decide +kernel
theorem contraction48_4 : (centerEquation Source.r48n residual (centers48 4) 3085 6 1024 4).check=true := by decide +kernel
theorem contraction48_5 : (centerEquation Source.r48n residual (centers48 5) 3085 6 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
