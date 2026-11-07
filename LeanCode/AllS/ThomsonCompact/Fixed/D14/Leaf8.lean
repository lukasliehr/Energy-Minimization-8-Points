import ThomsonCompact.Fixed.D14.Tab
import ThomsonCompact.Fixed.D14.Slice8

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D14

/-- Columns 97–106 of the D14 table identity at the radix. -/
theorem leaf8 : leafOk tab slice8 = true := by decide +kernel

end ThomsonCompact.Fixed.D14
