import ThomsonNegative.Certificate.Correction.q07.Row49

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction49_0 : (centerEquation Source.r49n residual (centers49 0) 3095 51 1024 0).check=true := by decide +kernel
theorem contraction49_1 : (centerEquation Source.r49n residual (centers49 1) 3095 51 1024 1).check=true := by decide +kernel
theorem contraction49_2 : (centerEquation Source.r49n residual (centers49 2) 3095 51 1024 2).check=true := by decide +kernel
theorem contraction49_3 : (centerEquation Source.r49n residual (centers49 3) 3095 51 1024 3).check=true := by decide +kernel
theorem contraction49_4 : (centerEquation Source.r49n residual (centers49 4) 3095 51 1024 4).check=true := by decide +kernel
theorem contraction49_5 : (centerEquation Source.r49n residual (centers49 5) 3095 51 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
