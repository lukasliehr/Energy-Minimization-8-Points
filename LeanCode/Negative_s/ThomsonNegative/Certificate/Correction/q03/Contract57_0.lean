import ThomsonNegative.Certificate.Correction.q03.Row57

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction57_0 : (centerEquation Source.r57n residual (centers57 0) 3085 6 1024 0).check=true := by decide +kernel
theorem contraction57_1 : (centerEquation Source.r57n residual (centers57 1) 3085 6 1024 1).check=true := by decide +kernel
theorem contraction57_2 : (centerEquation Source.r57n residual (centers57 2) 3085 6 1024 2).check=true := by decide +kernel
theorem contraction57_3 : (centerEquation Source.r57n residual (centers57 3) 3085 6 1024 3).check=true := by decide +kernel
theorem contraction57_4 : (centerEquation Source.r57n residual (centers57 4) 3085 6 1024 4).check=true := by decide +kernel
theorem contraction57_5 : (centerEquation Source.r57n residual (centers57 5) 3085 6 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
