import ThomsonCompact.CoeffMap.BProg

/-! One-time check (F2c): the sequential coefficient table of block 9, coordinates 50-74. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.CoeffMap

theorem eTabOk_09_50_75 : eTabOk 9 50 75 = true := by decide +kernel

end ThomsonCompact.CoeffMap
