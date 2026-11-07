import ThomsonNegative.Certificate.Correction.q01.Floor0_00
import ThomsonNegative.Certificate.Correction.q01.Floor0_01
import ThomsonNegative.Certificate.Correction.q01.Floor0_02
import ThomsonNegative.Certificate.Correction.q01.Floor0_03
import ThomsonNegative.Certificate.Correction.q01.Floor0_04
import ThomsonNegative.Certificate.Correction.q01.Floor0_05

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem floor0_checked : rowCheck 384 6 majorant0 weight0=true := by
  change ((((((true && rowCheckAt 384 6 majorant0 weight0 0) && rowCheckAt 384 6 majorant0 weight0 1) && rowCheckAt 384 6 majorant0 weight0 2) && rowCheckAt 384 6 majorant0 weight0 3) && rowCheckAt 384 6 majorant0 weight0 4) && rowCheckAt 384 6 majorant0 weight0 5)=true
  rw [floor0_0_checked, floor0_1_checked, floor0_2_checked, floor0_3_checked, floor0_4_checked, floor0_5_checked]
  rfl
end ThomsonNegative.Certificate.Correction.q01
