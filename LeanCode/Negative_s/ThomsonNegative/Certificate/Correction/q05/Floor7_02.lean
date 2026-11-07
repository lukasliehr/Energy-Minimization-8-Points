import ThomsonNegative.Certificate.Correction.q05.BlockData

namespace ThomsonNegative.Certificate.Correction.q05
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem floor7_2_checked : rowCheckAt 384 11 majorant7 weight7 2=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q05
