import ThomsonCompact.Fixed.D14.Tab
import ThomsonCompact.Fixed.D14.Slice6

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D14

/-- Columns 76–86 of the D14 table identity at the radix. -/
theorem leaf6 : leafOk tab slice6 = true := by decide +kernel

end ThomsonCompact.Fixed.D14
