import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice24

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 196–201 of the D16 table identity at the radix. -/
theorem leaf24 : leafOk tab slice24 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
