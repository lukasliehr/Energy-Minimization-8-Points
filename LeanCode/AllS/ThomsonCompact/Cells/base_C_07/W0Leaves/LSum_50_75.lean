import ThomsonCompact.CoeffMap.BSum
import ThomsonCompact.Cells.base_C_07.W0Sum

/-! W0 sum leaf of cell base_C_07: coordinates 50-74. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_C_07.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.Cells.C_base_C_07.W0

theorem lsum_50_75 : sumOk sumData 15 50 75 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_base_C_07.W0.Leaves
