import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice16

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 140–146 of the D16 table identity at the radix. -/
theorem leaf16 : leafOk tab slice16 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
