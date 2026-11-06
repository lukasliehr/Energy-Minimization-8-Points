import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice11

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 102–109 of the D16 table identity at the radix. -/
theorem leaf11 : leafOk tab slice11 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
