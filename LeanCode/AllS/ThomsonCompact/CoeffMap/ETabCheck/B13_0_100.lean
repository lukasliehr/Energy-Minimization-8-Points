import ThomsonCompact.CoeffMap.BProg

/-! One-time check (F2c): the sequential coefficient table of block 13, coordinates 0-99. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.CoeffMap

theorem eTabOk_13_0_100 : eTabOk 13 0 100 = true := by decide +kernel

end ThomsonCompact.CoeffMap
