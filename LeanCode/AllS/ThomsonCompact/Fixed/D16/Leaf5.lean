import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice5

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 52–60 of the D16 table identity at the radix. -/
theorem leaf5 : leafOk tab slice5 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
