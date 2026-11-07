import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice9

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 86–93 of the D16 table identity at the radix. -/
theorem leaf9 : leafOk tab slice9 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
