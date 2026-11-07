import ThomsonNegative.Certificate.Correction.q01.Row62

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction62_0 : (centerEquation Source.r62n residual (centers62 0) 3094 49 1024 0).check=true := by decide +kernel
theorem contraction62_1 : (centerEquation Source.r62n residual (centers62 1) 3094 49 1024 1).check=true := by decide +kernel
theorem contraction62_2 : (centerEquation Source.r62n residual (centers62 2) 3094 49 1024 2).check=true := by decide +kernel
theorem contraction62_3 : (centerEquation Source.r62n residual (centers62 3) 3094 49 1024 3).check=true := by decide +kernel
theorem contraction62_4 : (centerEquation Source.r62n residual (centers62 4) 3094 49 1024 4).check=true := by decide +kernel
theorem contraction62_5 : (centerEquation Source.r62n residual (centers62 5) 3094 49 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
