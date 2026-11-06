import ThomsonCompact.CoeffMap.BProg

/-! One-time check (F2c): the sequential coefficient table of block 9, coordinates 75-99. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.CoeffMap

theorem eTabOk_09_75_100 : eTabOk 9 75 100 = true := by decide +kernel

end ThomsonCompact.CoeffMap
