import ThomsonNegative.Certificate.Correction.q05.Row25

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction25_0 : (centerEquation Source.r25n residual (centers25 0) 3095 60 1024 0).check=true := by decide +kernel
theorem contraction25_1 : (centerEquation Source.r25n residual (centers25 1) 3095 60 1024 1).check=true := by decide +kernel
theorem contraction25_2 : (centerEquation Source.r25n residual (centers25 2) 3095 60 1024 2).check=true := by decide +kernel
theorem contraction25_3 : (centerEquation Source.r25n residual (centers25 3) 3095 60 1024 3).check=true := by decide +kernel
theorem contraction25_4 : (centerEquation Source.r25n residual (centers25 4) 3095 60 1024 4).check=true := by decide +kernel
theorem contraction25_5 : (centerEquation Source.r25n residual (centers25 5) 3095 60 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
