import ThomsonNegative.Certificate.Correction.q01.Row20

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction20_0 : (centerEquation Source.r20n residual (centers20 0) 3122 62 1033 0).check=true := by decide +kernel
theorem contraction20_1 : (centerEquation Source.r20n residual (centers20 1) 3122 62 1033 1).check=true := by decide +kernel
theorem contraction20_2 : (centerEquation Source.r20n residual (centers20 2) 3122 62 1033 2).check=true := by decide +kernel
theorem contraction20_3 : (centerEquation Source.r20n residual (centers20 3) 3122 62 1033 3).check=true := by decide +kernel
theorem contraction20_4 : (centerEquation Source.r20n residual (centers20 4) 3122 62 1033 4).check=true := by decide +kernel
theorem contraction20_5 : (centerEquation Source.r20n residual (centers20 5) 3122 62 1033 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
