import ThomsonCompact.Fixed.D14.Tab
import ThomsonCompact.Fixed.D14.Slice3

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D14

/-- Columns 42–53 of the D14 table identity at the radix. -/
theorem leaf3 : leafOk tab slice3 = true := by decide +kernel

end ThomsonCompact.Fixed.D14
