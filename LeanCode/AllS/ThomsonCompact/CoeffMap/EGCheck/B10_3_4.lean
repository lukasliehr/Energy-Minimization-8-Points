import ThomsonCompact.CoeffMap.BProg

/-! One-time check (F2c): the grouped coefficient lists of block 10, groups 3-3. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.CoeffMap

theorem eGOk_10_3_4 : eGOk 10 3 4 = true := by decide +kernel

end ThomsonCompact.CoeffMap
