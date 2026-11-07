import ThomsonCompact.Fixed.D14.Tab
import ThomsonCompact.Fixed.D14.Slice9

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D14

/-- Columns 107–116 of the D14 table identity at the radix. -/
theorem leaf9 : leafOk tab slice9 = true := by decide +kernel

end ThomsonCompact.Fixed.D14
