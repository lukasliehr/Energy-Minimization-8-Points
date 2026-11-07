import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.D16.Data
import ThomsonCompact.Cells.finite_d16_c68.W0Sum

/-! W0 sum leaf of cell finite_d16_c68: coordinates 22-43. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_finite_d16_c68.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_finite_d16_c68.W0

theorem lsum_22_44 : D16.L.sumOkD sumData 30 22 44 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_finite_d16_c68.W0.Leaves
