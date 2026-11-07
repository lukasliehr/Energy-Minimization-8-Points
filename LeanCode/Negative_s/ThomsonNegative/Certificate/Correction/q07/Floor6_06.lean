import ThomsonNegative.Certificate.Correction.q07.BlockData

namespace ThomsonNegative.Certificate.Correction.q07
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem floor6_6_checked : rowCheckAt 384 11 majorant6 weight6 6=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q07
