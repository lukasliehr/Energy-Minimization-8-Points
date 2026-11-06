import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice1

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 14–23 of the D16 table identity at the radix. -/
theorem leaf1 : leafOk tab slice1 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
