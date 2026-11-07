import ThomsonCompact.Fixed.D14.Tab
import ThomsonCompact.Fixed.D14.Slice0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D14

/-- Columns 0–16 of the D14 table identity at the radix. -/
theorem leaf0 : leafOk tab slice0 = true := by decide +kernel

end ThomsonCompact.Fixed.D14
