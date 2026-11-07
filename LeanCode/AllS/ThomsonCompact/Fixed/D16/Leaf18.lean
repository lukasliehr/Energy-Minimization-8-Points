import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice18

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 154–160 of the D16 table identity at the radix. -/
theorem leaf18 : leafOk tab slice18 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
