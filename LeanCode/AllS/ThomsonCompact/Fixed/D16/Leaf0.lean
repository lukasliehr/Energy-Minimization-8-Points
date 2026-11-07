import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice0

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 0–13 of the D16 table identity at the radix. -/
theorem leaf0 : leafOk tab slice0 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
