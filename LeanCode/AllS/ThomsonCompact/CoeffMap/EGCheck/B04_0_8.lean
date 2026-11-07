import ThomsonCompact.CoeffMap.BProg

/-! One-time check (F2c): the grouped coefficient lists of block 4, groups 0-7. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.CoeffMap

theorem eGOk_04_0_8 : eGOk 4 0 8 = true := by decide +kernel

end ThomsonCompact.CoeffMap
