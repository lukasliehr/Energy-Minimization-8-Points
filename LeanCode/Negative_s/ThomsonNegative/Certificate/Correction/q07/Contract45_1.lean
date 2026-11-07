import ThomsonNegative.Certificate.Correction.q07.Row45

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction45_6 : (centerEquation Source.r45n residual (centers45 6) 3078 1 1024 6).check=true := by decide +kernel
theorem contraction45_7 : (centerEquation Source.r45n residual (centers45 7) 3078 1 1024 7).check=true := by decide +kernel
theorem contraction45_8 : (centerEquation Source.r45n residual (centers45 8) 3078 1 1024 8).check=true := by decide +kernel
theorem contraction45_9 : (centerEquation Source.r45n residual (centers45 9) 3078 1 1024 9).check=true := by decide +kernel
theorem contraction45_10 : (centerEquation Source.r45n residual (centers45 10) 3078 1 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
