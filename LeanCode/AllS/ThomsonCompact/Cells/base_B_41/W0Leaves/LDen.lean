import ThomsonCompact.CoeffMap.KRows
import ThomsonCompact.Cells.base_B_41.W0Ctx

/-! Denominator leaf of cell base_B_41: no shared RF denominator vanishes on the cell (`denOk_sound`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_B_41.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.Cells.C_base_B_41.W0

theorem leaf_den : denOk ctx A = true := by decide +kernel

end ThomsonCompact.Cells.C_base_B_41.W0.Leaves
