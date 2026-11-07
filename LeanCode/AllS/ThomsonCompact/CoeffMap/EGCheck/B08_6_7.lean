import ThomsonCompact.CoeffMap.BProg

/-! One-time check (F2c): the grouped coefficient lists of block 8, groups 6-6. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.CoeffMap

theorem eGOk_08_6_7 : eGOk 8 6 7 = true := by decide +kernel

end ThomsonCompact.CoeffMap
