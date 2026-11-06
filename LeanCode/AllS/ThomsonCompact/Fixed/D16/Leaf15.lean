import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice15

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 132–139 of the D16 table identity at the radix. -/
theorem leaf15 : leafOk tab slice15 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
