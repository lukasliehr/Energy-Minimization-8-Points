import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.D16.Data
import ThomsonCompact.Cells.finite_d16_c56.W0Sum

/-! W0 sum leaf of cell finite_d16_c56: coordinates 25-49. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_finite_d16_c56.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_finite_d16_c56.W0

theorem lsum_25_50 : D16.L.sumOkD sumData 25 25 50 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_finite_d16_c56.W0.Leaves
