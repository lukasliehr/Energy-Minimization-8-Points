import ThomsonCompact.CoeffMap.BProg

/-! One-time check (F2c): the grouped coefficient lists of block 8, groups 7-7. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.CoeffMap

theorem eGOk_08_7_8 : eGOk 8 7 8 = true := by decide +kernel

end ThomsonCompact.CoeffMap
