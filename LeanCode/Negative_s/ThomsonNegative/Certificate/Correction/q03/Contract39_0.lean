import ThomsonNegative.Certificate.Correction.q03.Row39

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction39_0 : (centerEquation Source.r39n residual (centers39 0) 3095 60 1024 0).check=true := by decide +kernel
theorem contraction39_1 : (centerEquation Source.r39n residual (centers39 1) 3095 60 1024 1).check=true := by decide +kernel
theorem contraction39_2 : (centerEquation Source.r39n residual (centers39 2) 3095 60 1024 2).check=true := by decide +kernel
theorem contraction39_3 : (centerEquation Source.r39n residual (centers39 3) 3095 60 1024 3).check=true := by decide +kernel
theorem contraction39_4 : (centerEquation Source.r39n residual (centers39 4) 3095 60 1024 4).check=true := by decide +kernel
theorem contraction39_5 : (centerEquation Source.r39n residual (centers39 5) 3095 60 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
