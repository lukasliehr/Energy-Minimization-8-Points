import ThomsonNegative.Certificate.Correction.q03.Row54

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction54_0 : (centerEquation Source.r54n residual (centers54 0) 3085 6 1024 0).check=true := by decide +kernel
theorem contraction54_1 : (centerEquation Source.r54n residual (centers54 1) 3085 6 1024 1).check=true := by decide +kernel
theorem contraction54_2 : (centerEquation Source.r54n residual (centers54 2) 3085 6 1024 2).check=true := by decide +kernel
theorem contraction54_3 : (centerEquation Source.r54n residual (centers54 3) 3085 6 1024 3).check=true := by decide +kernel
theorem contraction54_4 : (centerEquation Source.r54n residual (centers54 4) 3085 6 1024 4).check=true := by decide +kernel
theorem contraction54_5 : (centerEquation Source.r54n residual (centers54 5) 3085 6 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
