import ThomsonNegative.Certificate.Correction.q01.Row44

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction44_0 : (centerEquation Source.r44n residual (centers44 0) 3085 6 1024 0).check=true := by decide +kernel
theorem contraction44_1 : (centerEquation Source.r44n residual (centers44 1) 3085 6 1024 1).check=true := by decide +kernel
theorem contraction44_2 : (centerEquation Source.r44n residual (centers44 2) 3085 6 1024 2).check=true := by decide +kernel
theorem contraction44_3 : (centerEquation Source.r44n residual (centers44 3) 3085 6 1024 3).check=true := by decide +kernel
theorem contraction44_4 : (centerEquation Source.r44n residual (centers44 4) 3085 6 1024 4).check=true := by decide +kernel
theorem contraction44_5 : (centerEquation Source.r44n residual (centers44 5) 3085 6 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
