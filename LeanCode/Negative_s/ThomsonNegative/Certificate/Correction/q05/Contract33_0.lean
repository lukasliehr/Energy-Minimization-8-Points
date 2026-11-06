import ThomsonNegative.Certificate.Correction.q05.Row33

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction33_0 : (centerEquation Source.r33n residual (centers33 0) 3095 60 1024 0).check=true := by decide +kernel
theorem contraction33_1 : (centerEquation Source.r33n residual (centers33 1) 3095 60 1024 1).check=true := by decide +kernel
theorem contraction33_2 : (centerEquation Source.r33n residual (centers33 2) 3095 60 1024 2).check=true := by decide +kernel
theorem contraction33_3 : (centerEquation Source.r33n residual (centers33 3) 3095 60 1024 3).check=true := by decide +kernel
theorem contraction33_4 : (centerEquation Source.r33n residual (centers33 4) 3095 60 1024 4).check=true := by decide +kernel
theorem contraction33_5 : (centerEquation Source.r33n residual (centers33 5) 3095 60 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
