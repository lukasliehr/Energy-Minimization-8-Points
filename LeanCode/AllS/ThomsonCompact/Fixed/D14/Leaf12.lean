import ThomsonCompact.Fixed.D14.Tab
import ThomsonCompact.Fixed.D14.Slice12

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D14

/-- Columns 136–144 of the D14 table identity at the radix. -/
theorem leaf12 : leafOk tab slice12 = true := by decide +kernel

end ThomsonCompact.Fixed.D14
