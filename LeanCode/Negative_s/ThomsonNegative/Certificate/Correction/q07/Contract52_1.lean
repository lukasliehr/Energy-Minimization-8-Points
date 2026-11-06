import ThomsonNegative.Certificate.Correction.q07.Row52

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction52_6 : (centerEquation Source.r52n residual (centers52 6) 3085 6 1024 6).check=true := by decide +kernel
theorem contraction52_7 : (centerEquation Source.r52n residual (centers52 7) 3085 6 1024 7).check=true := by decide +kernel
theorem contraction52_8 : (centerEquation Source.r52n residual (centers52 8) 3085 6 1024 8).check=true := by decide +kernel
theorem contraction52_9 : (centerEquation Source.r52n residual (centers52 9) 3085 6 1024 9).check=true := by decide +kernel
theorem contraction52_10 : (centerEquation Source.r52n residual (centers52 10) 3085 6 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
