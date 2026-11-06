import ThomsonCompact.Fixed.D14.STable

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D14

/-- The factorization of Q. -/
theorem fac_ok : facOk 448 gtab stab = true := by decide +kernel

end ThomsonCompact.Fixed.D14
