import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice23

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 189–195 of the D16 table identity at the radix. -/
theorem leaf23 : leafOk tab slice23 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
