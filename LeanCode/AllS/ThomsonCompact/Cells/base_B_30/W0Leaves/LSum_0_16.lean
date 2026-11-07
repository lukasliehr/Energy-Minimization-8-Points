import ThomsonCompact.CoeffMap.BSum
import ThomsonCompact.Cells.base_B_30.W0Sum

/-! W0 sum leaf of cell base_B_30: coordinates 0-15. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_B_30.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.Cells.C_base_B_30.W0

theorem lsum_0_16 : sumOk sumData 17 0 16 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_base_B_30.W0.Leaves
