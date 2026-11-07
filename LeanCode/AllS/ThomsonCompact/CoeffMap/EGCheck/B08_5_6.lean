import ThomsonCompact.CoeffMap.BProg

/-! One-time check (F2c): the grouped coefficient lists of block 8, groups 5-5. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.CoeffMap

theorem eGOk_08_5_6 : eGOk 8 5 6 = true := by decide +kernel

end ThomsonCompact.CoeffMap
