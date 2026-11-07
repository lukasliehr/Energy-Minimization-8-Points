import ThomsonNegative.Certificate.Correction.q09.Row54

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction54_6 : (centerEquation Source.r54n residual (centers54 6) 3085 6 1024 6).check=true := by decide +kernel
theorem contraction54_7 : (centerEquation Source.r54n residual (centers54 7) 3085 6 1024 7).check=true := by decide +kernel
theorem contraction54_8 : (centerEquation Source.r54n residual (centers54 8) 3085 6 1024 8).check=true := by decide +kernel
theorem contraction54_9 : (centerEquation Source.r54n residual (centers54 9) 3085 6 1024 9).check=true := by decide +kernel
theorem contraction54_10 : (centerEquation Source.r54n residual (centers54 10) 3085 6 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
