import ThomsonCompact.Fixed.D18c.LTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

/-- N link of outputs 182–271 (stored N(B) = canonical columns from κ and the raw tensors). -/
theorem link2 : linkOk tab ltab 90 182 = true := by decide +kernel

end ThomsonCompact.Fixed.D18c
