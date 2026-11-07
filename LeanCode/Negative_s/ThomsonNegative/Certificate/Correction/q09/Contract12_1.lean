import ThomsonNegative.Certificate.Correction.q09.Row12

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction12_6 : (centerEquation Source.r12n residual (centers12 6) 3078 1 1024 6).check=true := by decide +kernel
theorem contraction12_7 : (centerEquation Source.r12n residual (centers12 7) 3078 1 1024 7).check=true := by decide +kernel
theorem contraction12_8 : (centerEquation Source.r12n residual (centers12 8) 3078 1 1024 8).check=true := by decide +kernel
theorem contraction12_9 : (centerEquation Source.r12n residual (centers12 9) 3078 1 1024 9).check=true := by decide +kernel
theorem contraction12_10 : (centerEquation Source.r12n residual (centers12 10) 3078 1 1024 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
