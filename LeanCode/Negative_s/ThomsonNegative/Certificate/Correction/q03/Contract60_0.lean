import ThomsonNegative.Certificate.Correction.q03.Row60

namespace ThomsonNegative.Certificate.Correction.q03
open ThomsonNegative.Certificate.Correction
open ThomsonNegative.Structure.Exact
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem contraction60_0 : (centerEquation Source.r60n residual (centers60 0) 3085 6 1024 0).check=true := by decide +kernel
theorem contraction60_1 : (centerEquation Source.r60n residual (centers60 1) 3085 6 1024 1).check=true := by decide +kernel
theorem contraction60_2 : (centerEquation Source.r60n residual (centers60 2) 3085 6 1024 2).check=true := by decide +kernel
theorem contraction60_3 : (centerEquation Source.r60n residual (centers60 3) 3085 6 1024 3).check=true := by decide +kernel
theorem contraction60_4 : (centerEquation Source.r60n residual (centers60 4) 3085 6 1024 4).check=true := by decide +kernel
theorem contraction60_5 : (centerEquation Source.r60n residual (centers60 5) 3085 6 1024 5).check=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q03
