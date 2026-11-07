import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice12

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 110–116 of the D16 table identity at the radix. -/
theorem leaf12 : leafOk tab slice12 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
