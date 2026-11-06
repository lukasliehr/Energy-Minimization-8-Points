import ThomsonNegative.Certificate.Correction.q03.Row39

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction39_6 : (centerEquation Source.r39n residual (centers39 6) 3095 60 1024 6).check=true := by decide +kernel
theorem contraction39_7 : (centerEquation Source.r39n residual (centers39 7) 3095 60 1024 7).check=true := by decide +kernel
theorem contraction39_8 : (centerEquation Source.r39n residual (centers39 8) 3095 60 1024 8).check=true := by decide +kernel
theorem contraction39_9 : (centerEquation Source.r39n residual (centers39 9) 3095 60 1024 9).check=true := by decide +kernel
theorem contraction39_10 : (centerEquation Source.r39n residual (centers39 10) 3095 60 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
