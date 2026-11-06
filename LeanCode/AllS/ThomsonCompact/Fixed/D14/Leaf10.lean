import ThomsonCompact.Fixed.D14.Tab
import ThomsonCompact.Fixed.D14.Slice10

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D14

/-- Columns 117–126 of the D14 table identity at the radix. -/
theorem leaf10 : leafOk tab slice10 = true := by decide +kernel

end ThomsonCompact.Fixed.D14
