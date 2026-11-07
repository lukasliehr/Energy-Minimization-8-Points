import ThomsonCompact.CoeffMap.BProg

/-! One-time check (F2c): the grouped coefficient lists of block 2, groups 0-7. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.CoeffMap

theorem eGOk_02_0_8 : eGOk 2 0 8 = true := by decide +kernel

end ThomsonCompact.CoeffMap
