import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice3

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 34–42 of the D16 table identity at the radix. -/
theorem leaf3 : leafOk tab slice3 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
