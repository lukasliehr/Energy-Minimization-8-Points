import ThomsonCompact.Fixed.D14.LTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D14

/-- N link of outputs 0–72 (stored N(B) = canonical columns from κ and the raw tensors). -/
theorem link0 : linkOk tab ltab 73 0 = true := by decide +kernel

end ThomsonCompact.Fixed.D14
