import ThomsonCompact.Fixed.D18c.LTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

/-- N link of outputs 91–181 (stored N(B) = canonical columns from κ and the raw tensors). -/
theorem link1 : linkOk tab ltab 91 91 = true := by decide +kernel

end ThomsonCompact.Fixed.D18c
