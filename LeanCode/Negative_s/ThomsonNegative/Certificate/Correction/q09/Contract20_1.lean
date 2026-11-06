import ThomsonNegative.Certificate.Correction.q09.Row20

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction20_6 : (centerEquation Source.r20n residual (centers20 6) 3131 62 1036 6).check=true := by decide +kernel
theorem contraction20_7 : (centerEquation Source.r20n residual (centers20 7) 3131 62 1036 7).check=true := by decide +kernel
theorem contraction20_8 : (centerEquation Source.r20n residual (centers20 8) 3131 62 1036 8).check=true := by decide +kernel
theorem contraction20_9 : (centerEquation Source.r20n residual (centers20 9) 3131 62 1036 9).check=true := by decide +kernel
theorem contraction20_10 : (centerEquation Source.r20n residual (centers20 10) 3131 62 1036 10).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
