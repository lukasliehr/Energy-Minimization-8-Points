import ThomsonNegative.Certificate.Correction.q07.Row20

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction20_0 : (centerEquation Source.r20n residual (centers20 0) 3128 62 1035 0).check=true := by decide +kernel
theorem contraction20_1 : (centerEquation Source.r20n residual (centers20 1) 3128 62 1035 1).check=true := by decide +kernel
theorem contraction20_2 : (centerEquation Source.r20n residual (centers20 2) 3128 62 1035 2).check=true := by decide +kernel
theorem contraction20_3 : (centerEquation Source.r20n residual (centers20 3) 3128 62 1035 3).check=true := by decide +kernel
theorem contraction20_4 : (centerEquation Source.r20n residual (centers20 4) 3128 62 1035 4).check=true := by decide +kernel
theorem contraction20_5 : (centerEquation Source.r20n residual (centers20 5) 3128 62 1035 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
