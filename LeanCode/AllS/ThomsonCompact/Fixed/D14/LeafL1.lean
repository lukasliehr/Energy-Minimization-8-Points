import ThomsonCompact.Fixed.D14.LTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D14

/-- N link of outputs 73–144 (stored N(B) = canonical columns from κ and the raw tensors). -/
theorem link1 : linkOk tab ltab 72 73 = true := by decide +kernel

end ThomsonCompact.Fixed.D14
