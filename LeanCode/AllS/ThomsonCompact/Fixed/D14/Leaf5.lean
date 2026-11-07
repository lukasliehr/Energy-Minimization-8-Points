import ThomsonCompact.Fixed.D14.Tab
import ThomsonCompact.Fixed.D14.Slice5

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D14

/-- Columns 65–75 of the D14 table identity at the radix. -/
theorem leaf5 : leafOk tab slice5 = true := by decide +kernel

end ThomsonCompact.Fixed.D14
