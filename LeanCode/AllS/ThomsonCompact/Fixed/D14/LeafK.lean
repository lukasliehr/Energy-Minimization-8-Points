import ThomsonCompact.Fixed.D14.LTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D14

/-- Headers of the κ columns (`L ≤ 14`, `w ≤ 23`, raw rows `< 64`) and output blocks `< 4`. -/
theorem kap_ok : kapHdrOk ltab 145 14 23 64 = true := by decide +kernel

end ThomsonCompact.Fixed.D14
