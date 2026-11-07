import ThomsonNegative.Certificate.Correction.q07.Row41

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction41_0 : (centerEquation Source.r41n residual (centers41 0) 3095 54 1024 0).check=true := by decide +kernel
theorem contraction41_1 : (centerEquation Source.r41n residual (centers41 1) 3095 54 1024 1).check=true := by decide +kernel
theorem contraction41_2 : (centerEquation Source.r41n residual (centers41 2) 3095 54 1024 2).check=true := by decide +kernel
theorem contraction41_3 : (centerEquation Source.r41n residual (centers41 3) 3095 54 1024 3).check=true := by decide +kernel
theorem contraction41_4 : (centerEquation Source.r41n residual (centers41 4) 3095 54 1024 4).check=true := by decide +kernel
theorem contraction41_5 : (centerEquation Source.r41n residual (centers41 5) 3095 54 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
