import ThomsonNegative.Certificate.Correction.q03.Row00

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction0_0 : (centerEquation Source.r0n residual (centers0 0) 3094 47 1024 0).check=true := by decide +kernel
theorem contraction0_1 : (centerEquation Source.r0n residual (centers0 1) 3094 47 1024 1).check=true := by decide +kernel
theorem contraction0_2 : (centerEquation Source.r0n residual (centers0 2) 3094 47 1024 2).check=true := by decide +kernel
theorem contraction0_3 : (centerEquation Source.r0n residual (centers0 3) 3094 47 1024 3).check=true := by decide +kernel
theorem contraction0_4 : (centerEquation Source.r0n residual (centers0 4) 3094 47 1024 4).check=true := by decide +kernel
theorem contraction0_5 : (centerEquation Source.r0n residual (centers0 5) 3094 47 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
