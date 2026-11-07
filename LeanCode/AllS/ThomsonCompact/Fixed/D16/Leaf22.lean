import ThomsonCompact.Fixed.D16.Tab
import ThomsonCompact.Fixed.D16.Slice22

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Columns 182–188 of the D16 table identity at the radix. -/
theorem leaf22 : leafOk tab slice22 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
