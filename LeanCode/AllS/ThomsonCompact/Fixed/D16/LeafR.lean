import ThomsonCompact.Fixed.D16.STable

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Retained tag codes: pairwise distinct, none flagged non-retained. -/
theorem rtag_ok : rtagOk ltab 202 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
