import ThomsonCompact.CoeffMap.BProg

/-! One-time check (F2c): the grouped coefficient lists of block 9, groups 6-6. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.CoeffMap

theorem eGOk_09_6_7 : eGOk 9 6 7 = true := by decide +kernel

end ThomsonCompact.CoeffMap
