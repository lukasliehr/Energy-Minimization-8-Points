import ThomsonNegative.Certificate.Correction.q05.Row47

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction47_0 : (centerEquation Source.r47n residual (centers47 0) 3088 12 1024 0).check=true := by decide +kernel
theorem contraction47_1 : (centerEquation Source.r47n residual (centers47 1) 3088 12 1024 1).check=true := by decide +kernel
theorem contraction47_2 : (centerEquation Source.r47n residual (centers47 2) 3088 12 1024 2).check=true := by decide +kernel
theorem contraction47_3 : (centerEquation Source.r47n residual (centers47 3) 3088 12 1024 3).check=true := by decide +kernel
theorem contraction47_4 : (centerEquation Source.r47n residual (centers47 4) 3088 12 1024 4).check=true := by decide +kernel
theorem contraction47_5 : (centerEquation Source.r47n residual (centers47 5) 3088 12 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
