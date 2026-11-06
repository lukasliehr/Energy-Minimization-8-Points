import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.D16.Data
import ThomsonCompact.Cells.finite_d16_c56.W0Ctx
import ThomsonCompact.Cells.finite_d16_c56.W0Sum

/-! Denominator leaf of cell finite_d16_c56: no shared RF denominator vanishes on the cell; the owner parts partition. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_finite_d16_c56.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_finite_d16_c56.W0

theorem leaf_den : D16.L.denOkD ctx A sumData = true := by decide +kernel

end ThomsonCompact.Cells.C_finite_d16_c56.W0.Leaves
