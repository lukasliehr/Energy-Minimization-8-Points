import ThomsonNegative.Certificate.Correction.q07.Row43

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction43_6 : (centerEquation Source.r43n residual (centers43 6) 3094 41 1024 6).check=true := by decide +kernel
theorem contraction43_7 : (centerEquation Source.r43n residual (centers43 7) 3094 41 1024 7).check=true := by decide +kernel
theorem contraction43_8 : (centerEquation Source.r43n residual (centers43 8) 3094 41 1024 8).check=true := by decide +kernel
theorem contraction43_9 : (centerEquation Source.r43n residual (centers43 9) 3094 41 1024 9).check=true := by decide +kernel
theorem contraction43_10 : (centerEquation Source.r43n residual (centers43 10) 3094 41 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
