import ThomsonCompact.Fixed.D18c.LTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

/-- N link of outputs 0–90 (stored N(B) = canonical columns from κ and the raw tensors). -/
theorem link0 : linkOk tab ltab 91 0 = true := by decide +kernel

end ThomsonCompact.Fixed.D18c
