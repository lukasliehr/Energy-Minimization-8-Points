import ThomsonNegative.Certificate.Correction.q01.Row28

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction28_0 : (centerEquation Source.r28n residual (centers28 0) 3089 13 1024 0).check=true := by decide +kernel
theorem contraction28_1 : (centerEquation Source.r28n residual (centers28 1) 3089 13 1024 1).check=true := by decide +kernel
theorem contraction28_2 : (centerEquation Source.r28n residual (centers28 2) 3089 13 1024 2).check=true := by decide +kernel
theorem contraction28_3 : (centerEquation Source.r28n residual (centers28 3) 3089 13 1024 3).check=true := by decide +kernel
theorem contraction28_4 : (centerEquation Source.r28n residual (centers28 4) 3089 13 1024 4).check=true := by decide +kernel
theorem contraction28_5 : (centerEquation Source.r28n residual (centers28 5) 3089 13 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
