import ThomsonCompact.Fixed.D14.Tab
import ThomsonCompact.Fixed.D14.Slice1

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D14

/-- Columns 17–29 of the D14 table identity at the radix. -/
theorem leaf1 : leafOk tab slice1 = true := by decide +kernel

end ThomsonCompact.Fixed.D14
