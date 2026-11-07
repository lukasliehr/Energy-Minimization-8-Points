import ThomsonCompact.CoeffMap.BProg

/-! One-time check (F2c): the sequential coefficient table of block 10, coordinates 50-99. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.CoeffMap

theorem eTabOk_10_50_100 : eTabOk 10 50 100 = true := by decide +kernel

end ThomsonCompact.CoeffMap
