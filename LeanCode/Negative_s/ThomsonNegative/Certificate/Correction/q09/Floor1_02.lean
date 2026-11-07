import ThomsonNegative.Certificate.Correction.q09.BlockData

namespace ThomsonNegative.Certificate.Correction.q09
open ThomsonNegative.Certificate.Correction
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem floor1_2_checked : rowCheckAt 384 5 majorant1 weight1 2=true := by decide +kernel
end ThomsonNegative.Certificate.Correction.q09
