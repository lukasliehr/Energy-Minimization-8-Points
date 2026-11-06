import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice7

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 70–77 of the D16 table identity at the radix. -/
theorem leaf7 : leafOk tab slice7 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
