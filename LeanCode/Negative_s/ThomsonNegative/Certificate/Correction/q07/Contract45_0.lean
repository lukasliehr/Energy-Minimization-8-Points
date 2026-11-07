import ThomsonNegative.Certificate.Correction.q07.Row45

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction45_0 : (centerEquation Source.r45n residual (centers45 0) 3078 1 1024 0).check=true := by decide +kernel
theorem contraction45_1 : (centerEquation Source.r45n residual (centers45 1) 3078 1 1024 1).check=true := by decide +kernel
theorem contraction45_2 : (centerEquation Source.r45n residual (centers45 2) 3078 1 1024 2).check=true := by decide +kernel
theorem contraction45_3 : (centerEquation Source.r45n residual (centers45 3) 3078 1 1024 3).check=true := by decide +kernel
theorem contraction45_4 : (centerEquation Source.r45n residual (centers45 4) 3078 1 1024 4).check=true := by decide +kernel
theorem contraction45_5 : (centerEquation Source.r45n residual (centers45 5) 3078 1 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
