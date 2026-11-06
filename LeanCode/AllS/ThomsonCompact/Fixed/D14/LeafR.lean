import ThomsonCompact.Fixed.D14.STable

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D14

/-- Retained tag codes: pairwise distinct, none flagged non-retained. -/
theorem rtag_ok : rtagOk ltab 145 = true := by decide +kernel

end ThomsonCompact.Fixed.D14
