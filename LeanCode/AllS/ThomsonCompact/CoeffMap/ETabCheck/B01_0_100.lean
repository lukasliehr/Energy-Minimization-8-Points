import ThomsonCompact.CoeffMap.BProg

/-! One-time check (F2c): the sequential coefficient table of block 1, coordinates 0-99. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.CoeffMap

theorem eTabOk_01_0_100 : eTabOk 1 0 100 = true := by decide +kernel

end ThomsonCompact.CoeffMap
