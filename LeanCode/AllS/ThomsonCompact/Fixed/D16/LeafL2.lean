import ThomsonCompact.Fixed.D16.LTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- N link of outputs 82–122 (stored N(B) = canonical columns from κ and the raw tensors). -/
theorem link2 : linkOk tab ltab 41 82 = true := by decide +kernel

end ThomsonCompact.Fixed.D16
