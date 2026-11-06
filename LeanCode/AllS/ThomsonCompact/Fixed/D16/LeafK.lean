import ThomsonCompact.Fixed.D16.LTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- Headers of the κ columns (`L ≤ 15`, `w ≤ 26`, raw rows `< 64`) and output blocks `< 4`. -/
theorem kap_ok : kapHdrOk ltab 202 15 26 64 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
