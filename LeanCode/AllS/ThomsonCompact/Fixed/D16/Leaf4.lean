import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice4

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 43–51 of the D16 table identity at the radix. -/
theorem leaf4 : leafOk tab slice4 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
