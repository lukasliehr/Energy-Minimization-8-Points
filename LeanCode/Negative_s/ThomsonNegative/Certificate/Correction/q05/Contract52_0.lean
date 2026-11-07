import ThomsonNegative.Certificate.Correction.q05.Row52

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction52_0 : (centerEquation Source.r52n residual (centers52 0) 3085 6 1024 0).check=true := by decide +kernel
theorem contraction52_1 : (centerEquation Source.r52n residual (centers52 1) 3085 6 1024 1).check=true := by decide +kernel
theorem contraction52_2 : (centerEquation Source.r52n residual (centers52 2) 3085 6 1024 2).check=true := by decide +kernel
theorem contraction52_3 : (centerEquation Source.r52n residual (centers52 3) 3085 6 1024 3).check=true := by decide +kernel
theorem contraction52_4 : (centerEquation Source.r52n residual (centers52 4) 3085 6 1024 4).check=true := by decide +kernel
theorem contraction52_5 : (centerEquation Source.r52n residual (centers52 5) 3085 6 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
