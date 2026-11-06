import ThomsonNegative.Certificate.Correction.q07.Floor6_00
import ThomsonNegative.Certificate.Correction.q07.Floor6_01
import ThomsonNegative.Certificate.Correction.q07.Floor6_02
import ThomsonNegative.Certificate.Correction.q07.Floor6_03
import ThomsonNegative.Certificate.Correction.q07.Floor6_04
import ThomsonNegative.Certificate.Correction.q07.Floor6_05
import ThomsonNegative.Certificate.Correction.q07.Floor6_06
import ThomsonNegative.Certificate.Correction.q07.Floor6_07
import ThomsonNegative.Certificate.Correction.q07.Floor6_08
import ThomsonNegative.Certificate.Correction.q07.Floor6_09
import ThomsonNegative.Certificate.Correction.q07.Floor6_10

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem floor6_checked : rowCheck 384 11 majorant6 weight6=true := by
  change (((((((((((true && rowCheckAt 384 11 majorant6 weight6 0) && rowCheckAt 384 11 majorant6 weight6 1) && rowCheckAt 384 11 majorant6 weight6 2) && rowCheckAt 384 11 majorant6 weight6 3) && rowCheckAt 384 11 majorant6 weight6 4) && rowCheckAt 384 11 majorant6 weight6 5) && rowCheckAt 384 11 majorant6 weight6 6) && rowCheckAt 384 11 majorant6 weight6 7) && rowCheckAt 384 11 majorant6 weight6 8) && rowCheckAt 384 11 majorant6 weight6 9) && rowCheckAt 384 11 majorant6 weight6 10)=true
  rw [floor6_0_checked, floor6_1_checked, floor6_2_checked, floor6_3_checked, floor6_4_checked, floor6_5_checked, floor6_6_checked, floor6_7_checked, floor6_8_checked, floor6_9_checked, floor6_10_checked]
  rfl
end ThomsonNegative.Certificate.Correction.q07
