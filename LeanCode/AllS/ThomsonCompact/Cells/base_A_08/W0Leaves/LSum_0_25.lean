import ThomsonCompact.CoeffMap.BSum
import ThomsonCompact.Cells.base_A_08.W0Sum

/-! W0 sum leaf of cell base_A_08: coordinates 0-24. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_A_08.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.Cells.C_base_A_08.W0

theorem lsum_0_25 : sumOk sumData 14 0 25 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_base_A_08.W0.Leaves
