import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice19

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 161–167 of the D16 table identity at the radix. -/
theorem leaf19 : leafOk tab slice19 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
