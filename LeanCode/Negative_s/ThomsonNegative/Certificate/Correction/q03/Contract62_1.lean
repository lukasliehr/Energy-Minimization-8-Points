import ThomsonNegative.Certificate.Correction.q03.Row62

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction62_6 : (centerEquation Source.r62n residual (centers62 6) 3094 49 1024 6).check=true := by decide +kernel
theorem contraction62_7 : (centerEquation Source.r62n residual (centers62 7) 3094 49 1024 7).check=true := by decide +kernel
theorem contraction62_8 : (centerEquation Source.r62n residual (centers62 8) 3094 49 1024 8).check=true := by decide +kernel
theorem contraction62_9 : (centerEquation Source.r62n residual (centers62 9) 3094 49 1024 9).check=true := by decide +kernel
theorem contraction62_10 : (centerEquation Source.r62n residual (centers62 10) 3094 49 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
