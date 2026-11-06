import ThomsonCompact.CoeffMap.BProg

/-! One-time check (F2c): the sequential coefficient table of block 12, coordinates 0-99. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.CoeffMap

theorem eTabOk_12_0_100 : eTabOk 12 0 100 = true := by decide +kernel

end ThomsonCompact.CoeffMap
