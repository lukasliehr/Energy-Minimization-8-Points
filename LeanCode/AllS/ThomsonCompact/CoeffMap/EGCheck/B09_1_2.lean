import ThomsonCompact.CoeffMap.BProg

/-! One-time check (F2c): the grouped coefficient lists of block 9, groups 1-1. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.CoeffMap

theorem eGOk_09_1_2 : eGOk 9 1 2 = true := by decide +kernel

end ThomsonCompact.CoeffMap
