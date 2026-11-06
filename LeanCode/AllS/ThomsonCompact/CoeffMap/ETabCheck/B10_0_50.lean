import ThomsonCompact.CoeffMap.BProg

/-! One-time check (F2c): the sequential coefficient table of block 10, coordinates 0-49. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.CoeffMap

theorem eTabOk_10_0_50 : eTabOk 10 0 50 = true := by decide +kernel

end ThomsonCompact.CoeffMap
