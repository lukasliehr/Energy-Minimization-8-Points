import ThomsonCompact.Fixed.D14.Tab
import ThomsonCompact.Fixed.D14.Slice4

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D14

/-- Columns 54–64 of the D14 table identity at the radix. -/
theorem leaf4 : leafOk tab slice4 = true := by decide +kernel

end ThomsonCompact.Fixed.D14
