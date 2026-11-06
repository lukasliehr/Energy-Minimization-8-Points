import ThomsonNegative.Certificate.Correction.q01.Row67

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction67_0 : (centerEquation Source.r67n residual (centers67 0) 3085 6 1024 0).check=true := by decide +kernel
theorem contraction67_1 : (centerEquation Source.r67n residual (centers67 1) 3085 6 1024 1).check=true := by decide +kernel
theorem contraction67_2 : (centerEquation Source.r67n residual (centers67 2) 3085 6 1024 2).check=true := by decide +kernel
theorem contraction67_3 : (centerEquation Source.r67n residual (centers67 3) 3085 6 1024 3).check=true := by decide +kernel
theorem contraction67_4 : (centerEquation Source.r67n residual (centers67 4) 3085 6 1024 4).check=true := by decide +kernel
theorem contraction67_5 : (centerEquation Source.r67n residual (centers67 5) 3085 6 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
