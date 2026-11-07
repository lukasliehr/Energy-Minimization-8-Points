import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice6

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 61–69 of the D16 table identity at the radix. -/
theorem leaf6 : leafOk tab slice6 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
