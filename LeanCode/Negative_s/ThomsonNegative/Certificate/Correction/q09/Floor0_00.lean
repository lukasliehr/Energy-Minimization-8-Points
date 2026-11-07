import ThomsonNegative.Certificate.Correction.q09.BlockData

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem floor0_0_checked : rowCheckAt 384 6 majorant0 weight0 0=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
