import ThomsonNegative.Certificate.Correction.q01.Row27

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction27_0 : (centerEquation Source.r27n residual (centers27 0) 3095 60 1024 0).check=true := by decide +kernel
theorem contraction27_1 : (centerEquation Source.r27n residual (centers27 1) 3095 60 1024 1).check=true := by decide +kernel
theorem contraction27_2 : (centerEquation Source.r27n residual (centers27 2) 3095 60 1024 2).check=true := by decide +kernel
theorem contraction27_3 : (centerEquation Source.r27n residual (centers27 3) 3095 60 1024 3).check=true := by decide +kernel
theorem contraction27_4 : (centerEquation Source.r27n residual (centers27 4) 3095 60 1024 4).check=true := by decide +kernel
theorem contraction27_5 : (centerEquation Source.r27n residual (centers27 5) 3095 60 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
