import ThomsonNegative.Certificate.Correction.q01.Row28

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction28_6 : (centerEquation Source.r28n residual (centers28 6) 3089 13 1024 6).check=true := by decide +kernel
theorem contraction28_7 : (centerEquation Source.r28n residual (centers28 7) 3089 13 1024 7).check=true := by decide +kernel
theorem contraction28_8 : (centerEquation Source.r28n residual (centers28 8) 3089 13 1024 8).check=true := by decide +kernel
theorem contraction28_9 : (centerEquation Source.r28n residual (centers28 9) 3089 13 1024 9).check=true := by decide +kernel
theorem contraction28_10 : (centerEquation Source.r28n residual (centers28 10) 3089 13 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
