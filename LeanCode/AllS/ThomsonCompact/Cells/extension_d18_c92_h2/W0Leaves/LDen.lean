import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.D18.Data
import ThomsonCompact.Cells.extension_d18_c92_h2.W0Ctx
import ThomsonCompact.Cells.extension_d18_c92_h2.W0Sum

/-! Denominator leaf of cell extension_d18_c92_h2: no shared RF denominator vanishes on the cell; the owner parts partition. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_extension_d18_c92_h2.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_extension_d18_c92_h2.W0

theorem leaf_den : D18.L.denOkD ctx A sumData = true := by decide +kernel

end ThomsonCompact.Cells.C_extension_d18_c92_h2.W0.Leaves
