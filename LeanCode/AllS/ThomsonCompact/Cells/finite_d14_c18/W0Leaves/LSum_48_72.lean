import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.D14.Data
import ThomsonCompact.Cells.finite_d14_c18.W0Sum

/-! W0 sum leaf of cell finite_d14_c18: coordinates 48-71. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_finite_d14_c18.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_finite_d14_c18.W0

theorem lsum_48_72 : D14.L.sumOkD sumData 28 48 72 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_finite_d14_c18.W0.Leaves
