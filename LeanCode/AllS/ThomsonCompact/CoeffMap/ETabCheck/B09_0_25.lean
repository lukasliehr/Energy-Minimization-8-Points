import ThomsonCompact.CoeffMap.BProg

/-! One-time check (F2c): the sequential coefficient table of block 9, coordinates 0-24. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.CoeffMap

theorem eTabOk_09_0_25 : eTabOk 9 0 25 = true := by decide +kernel

end ThomsonCompact.CoeffMap
