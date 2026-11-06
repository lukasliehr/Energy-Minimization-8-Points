import ThomsonNegative.Certificate.Correction.q01.BlockData

namespace ThomsonNegative.Certificate.Correction.q01
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem floor6_5_checked : rowCheckAt 384 11 majorant6 weight6 5=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q01
