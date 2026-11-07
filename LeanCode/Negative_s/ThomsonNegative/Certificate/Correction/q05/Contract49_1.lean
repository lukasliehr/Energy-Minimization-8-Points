import ThomsonNegative.Certificate.Correction.q05.Row49

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction49_6 : (centerEquation Source.r49n residual (centers49 6) 3095 51 1024 6).check=true := by decide +kernel
theorem contraction49_7 : (centerEquation Source.r49n residual (centers49 7) 3095 51 1024 7).check=true := by decide +kernel
theorem contraction49_8 : (centerEquation Source.r49n residual (centers49 8) 3095 51 1024 8).check=true := by decide +kernel
theorem contraction49_9 : (centerEquation Source.r49n residual (centers49 9) 3095 51 1024 9).check=true := by decide +kernel
theorem contraction49_10 : (centerEquation Source.r49n residual (centers49 10) 3095 51 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
