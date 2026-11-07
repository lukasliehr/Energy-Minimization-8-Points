import ThomsonCompact.Fixed.D14.Tab
import ThomsonCompact.Fixed.D14.Slice11

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D14

/-- Columns 127–135 of the D14 table identity at the radix. -/
theorem leaf11 : leafOk tab slice11 = true := by decide +kernel

end ThomsonCompact.Fixed.D14
