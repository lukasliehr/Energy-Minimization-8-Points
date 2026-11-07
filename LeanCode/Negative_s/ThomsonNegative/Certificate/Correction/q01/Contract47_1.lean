import ThomsonNegative.Certificate.Correction.q01.Row47

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction47_6 : (centerEquation Source.r47n residual (centers47 6) 3088 12 1024 6).check=true := by decide +kernel
theorem contraction47_7 : (centerEquation Source.r47n residual (centers47 7) 3088 12 1024 7).check=true := by decide +kernel
theorem contraction47_8 : (centerEquation Source.r47n residual (centers47 8) 3088 12 1024 8).check=true := by decide +kernel
theorem contraction47_9 : (centerEquation Source.r47n residual (centers47 9) 3088 12 1024 9).check=true := by decide +kernel
theorem contraction47_10 : (centerEquation Source.r47n residual (centers47 10) 3088 12 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
