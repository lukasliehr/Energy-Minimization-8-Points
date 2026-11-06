import ThomsonNegative.Certificate.Correction.q05.Row55

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction55_0 : (centerEquation Source.r55n residual (centers55 0) 3085 6 1024 0).check=true := by decide +kernel
theorem contraction55_1 : (centerEquation Source.r55n residual (centers55 1) 3085 6 1024 1).check=true := by decide +kernel
theorem contraction55_2 : (centerEquation Source.r55n residual (centers55 2) 3085 6 1024 2).check=true := by decide +kernel
theorem contraction55_3 : (centerEquation Source.r55n residual (centers55 3) 3085 6 1024 3).check=true := by decide +kernel
theorem contraction55_4 : (centerEquation Source.r55n residual (centers55 4) 3085 6 1024 4).check=true := by decide +kernel
theorem contraction55_5 : (centerEquation Source.r55n residual (centers55 5) 3085 6 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
