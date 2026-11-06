import ThomsonNegative.Certificate.Correction.q07.Row08

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction8_6 : (centerEquation Source.r8n residual (centers8 6) 3094 43 1024 6).check=true := by decide +kernel
theorem contraction8_7 : (centerEquation Source.r8n residual (centers8 7) 3094 43 1024 7).check=true := by decide +kernel
theorem contraction8_8 : (centerEquation Source.r8n residual (centers8 8) 3094 43 1024 8).check=true := by decide +kernel
theorem contraction8_9 : (centerEquation Source.r8n residual (centers8 9) 3094 43 1024 9).check=true := by decide +kernel
theorem contraction8_10 : (centerEquation Source.r8n residual (centers8 10) 3094 43 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
