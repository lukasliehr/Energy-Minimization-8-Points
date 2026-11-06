import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice2

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 24–33 of the D16 table identity at the radix. -/
theorem leaf2 : leafOk tab slice2 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
