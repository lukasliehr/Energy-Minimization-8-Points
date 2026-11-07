import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice13

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 117–124 of the D16 table identity at the radix. -/
theorem leaf13 : leafOk tab slice13 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
