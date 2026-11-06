import ThomsonNegative.Certificate.Correction.q05.Row08

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction8_0 : (centerEquation Source.r8n residual (centers8 0) 3094 43 1024 0).check=true := by decide +kernel
theorem contraction8_1 : (centerEquation Source.r8n residual (centers8 1) 3094 43 1024 1).check=true := by decide +kernel
theorem contraction8_2 : (centerEquation Source.r8n residual (centers8 2) 3094 43 1024 2).check=true := by decide +kernel
theorem contraction8_3 : (centerEquation Source.r8n residual (centers8 3) 3094 43 1024 3).check=true := by decide +kernel
theorem contraction8_4 : (centerEquation Source.r8n residual (centers8 4) 3094 43 1024 4).check=true := by decide +kernel
theorem contraction8_5 : (centerEquation Source.r8n residual (centers8 5) 3094 43 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
