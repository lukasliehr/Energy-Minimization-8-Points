import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice10

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 94–101 of the D16 table identity at the radix. -/
theorem leaf10 : leafOk tab slice10 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
