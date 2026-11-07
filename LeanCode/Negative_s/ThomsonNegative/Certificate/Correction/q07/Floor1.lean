import ThomsonNegative.Certificate.Correction.q07.Floor1_00
import ThomsonNegative.Certificate.Correction.q07.Floor1_01
import ThomsonNegative.Certificate.Correction.q07.Floor1_02
import ThomsonNegative.Certificate.Correction.q07.Floor1_03
import ThomsonNegative.Certificate.Correction.q07.Floor1_04

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem floor1_checked : rowCheck 384 5 majorant1 weight1=true := by
  change (((((true && rowCheckAt 384 5 majorant1 weight1 0) && rowCheckAt 384 5 majorant1 weight1 1) && rowCheckAt 384 5 majorant1 weight1 2) && rowCheckAt 384 5 majorant1 weight1 3) && rowCheckAt 384 5 majorant1 weight1 4)=true
  rw [floor1_0_checked, floor1_1_checked, floor1_2_checked, floor1_3_checked, floor1_4_checked]
  rfl
end ThomsonNegative.Certificate.Correction.q07
