import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice21

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 175–181 of the D16 table identity at the radix. -/
theorem leaf21 : leafOk tab slice21 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
