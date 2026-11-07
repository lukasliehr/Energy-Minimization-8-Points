import ThomsonNegative.Certificate.Correction.q01.Row12

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction12_0 : (centerEquation Source.r12n residual (centers12 0) 3078 1 1024 0).check=true := by decide +kernel
theorem contraction12_1 : (centerEquation Source.r12n residual (centers12 1) 3078 1 1024 1).check=true := by decide +kernel
theorem contraction12_2 : (centerEquation Source.r12n residual (centers12 2) 3078 1 1024 2).check=true := by decide +kernel
theorem contraction12_3 : (centerEquation Source.r12n residual (centers12 3) 3078 1 1024 3).check=true := by decide +kernel
theorem contraction12_4 : (centerEquation Source.r12n residual (centers12 4) 3078 1 1024 4).check=true := by decide +kernel
theorem contraction12_5 : (centerEquation Source.r12n residual (centers12 5) 3078 1 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
