import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice14

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 125–131 of the D16 table identity at the radix. -/
theorem leaf14 : leafOk tab slice14 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
