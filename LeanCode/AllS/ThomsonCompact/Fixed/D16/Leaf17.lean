import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice17

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 147–153 of the D16 table identity at the radix. -/
theorem leaf17 : leafOk tab slice17 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
