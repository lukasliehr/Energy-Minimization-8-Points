import ThomsonCompact.Fixed.D14.Tab
import ThomsonCompact.Fixed.D14.Slice7

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D14

/-- Columns 87–96 of the D14 table identity at the radix. -/
theorem leaf7 : leafOk tab slice7 = true := by decide +kernel

end ThomsonCompact.Fixed.D14
