import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.D18.Data
import ThomsonCompact.Cells.extension_d18_c92_h2.W0Sum

/-! W0 sum leaf of cell extension_d18_c92_h2: coordinates 0-18. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_extension_d18_c92_h2.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_extension_d18_c92_h2.W0

theorem lsum_0_19 : D18.L.sumOkD sumData 22 0 19 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_extension_d18_c92_h2.W0.Leaves
