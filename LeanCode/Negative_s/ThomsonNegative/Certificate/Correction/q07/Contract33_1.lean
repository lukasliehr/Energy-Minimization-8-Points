import ThomsonNegative.Certificate.Correction.q07.Row33

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction33_6 : (centerEquation Source.r33n residual (centers33 6) 3095 60 1024 6).check=true := by decide +kernel
theorem contraction33_7 : (centerEquation Source.r33n residual (centers33 7) 3095 60 1024 7).check=true := by decide +kernel
theorem contraction33_8 : (centerEquation Source.r33n residual (centers33 8) 3095 60 1024 8).check=true := by decide +kernel
theorem contraction33_9 : (centerEquation Source.r33n residual (centers33 9) 3095 60 1024 9).check=true := by decide +kernel
theorem contraction33_10 : (centerEquation Source.r33n residual (centers33 10) 3095 60 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
