import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice20

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 168–174 of the D16 table identity at the radix. -/
theorem leaf20 : leafOk tab slice20 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
