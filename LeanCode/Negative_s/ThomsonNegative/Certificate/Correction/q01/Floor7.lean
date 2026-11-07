import ThomsonNegative.Certificate.Correction.q01.Floor7_00
import ThomsonNegative.Certificate.Correction.q01.Floor7_01
import ThomsonNegative.Certificate.Correction.q01.Floor7_02
import ThomsonNegative.Certificate.Correction.q01.Floor7_03
import ThomsonNegative.Certificate.Correction.q01.Floor7_04
import ThomsonNegative.Certificate.Correction.q01.Floor7_05
import ThomsonNegative.Certificate.Correction.q01.Floor7_06
import ThomsonNegative.Certificate.Correction.q01.Floor7_07
import ThomsonNegative.Certificate.Correction.q01.Floor7_08
import ThomsonNegative.Certificate.Correction.q01.Floor7_09
import ThomsonNegative.Certificate.Correction.q01.Floor7_10

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem floor7_checked : rowCheck 384 11 majorant7 weight7=true := by
  change (((((((((((true && rowCheckAt 384 11 majorant7 weight7 0) && rowCheckAt 384 11 majorant7 weight7 1) && rowCheckAt 384 11 majorant7 weight7 2) && rowCheckAt 384 11 majorant7 weight7 3) && rowCheckAt 384 11 majorant7 weight7 4) && rowCheckAt 384 11 majorant7 weight7 5) && rowCheckAt 384 11 majorant7 weight7 6) && rowCheckAt 384 11 majorant7 weight7 7) && rowCheckAt 384 11 majorant7 weight7 8) && rowCheckAt 384 11 majorant7 weight7 9) && rowCheckAt 384 11 majorant7 weight7 10)=true
  rw [floor7_0_checked, floor7_1_checked, floor7_2_checked, floor7_3_checked, floor7_4_checked, floor7_5_checked, floor7_6_checked, floor7_7_checked, floor7_8_checked, floor7_9_checked, floor7_10_checked]
  rfl
end ThomsonNegative.Certificate.Correction.q01
