import ThomsonNegative.Certificate.Correction.q07.Row25

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction25_6 : (centerEquation Source.r25n residual (centers25 6) 3095 60 1024 6).check=true := by decide +kernel
theorem contraction25_7 : (centerEquation Source.r25n residual (centers25 7) 3095 60 1024 7).check=true := by decide +kernel
theorem contraction25_8 : (centerEquation Source.r25n residual (centers25 8) 3095 60 1024 8).check=true := by decide +kernel
theorem contraction25_9 : (centerEquation Source.r25n residual (centers25 9) 3095 60 1024 9).check=true := by decide +kernel
theorem contraction25_10 : (centerEquation Source.r25n residual (centers25 10) 3095 60 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
