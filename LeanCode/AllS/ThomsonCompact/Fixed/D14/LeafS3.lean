import ThomsonCompact.Fixed.D14.STable

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D14

/-- The m0Standard κ entries are their RF records times δ_b. -/
theorem rf3_ok : rfOk 448 gtab ltab stab 14 23 3 = true := by decide +kernel

end ThomsonCompact.Fixed.D14
