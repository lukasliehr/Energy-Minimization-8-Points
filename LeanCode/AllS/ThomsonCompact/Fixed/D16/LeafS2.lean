import ThomsonCompact.Fixed.D16.STable

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- The m0Plus κ entries are their RF records times δ_b. -/
theorem rf2_ok : rfOk 448 gtab ltab stab 15 26 2 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
