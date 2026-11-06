import ThomsonNegative.Certificate.Correction.q03.Row66

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction66_0 : (centerEquation Source.r66n residual (centers66 0) 3085 6 1024 0).check=true := by decide +kernel
theorem contraction66_1 : (centerEquation Source.r66n residual (centers66 1) 3085 6 1024 1).check=true := by decide +kernel
theorem contraction66_2 : (centerEquation Source.r66n residual (centers66 2) 3085 6 1024 2).check=true := by decide +kernel
theorem contraction66_3 : (centerEquation Source.r66n residual (centers66 3) 3085 6 1024 3).check=true := by decide +kernel
theorem contraction66_4 : (centerEquation Source.r66n residual (centers66 4) 3085 6 1024 4).check=true := by decide +kernel
theorem contraction66_5 : (centerEquation Source.r66n residual (centers66 5) 3085 6 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
