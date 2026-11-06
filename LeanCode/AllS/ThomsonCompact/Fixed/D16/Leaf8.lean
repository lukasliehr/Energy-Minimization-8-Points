import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice8

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 78–85 of the D16 table identity at the radix. -/
theorem leaf8 : leafOk tab slice8 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
