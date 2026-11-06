import ThomsonCompact.CoeffMap.BSum
import ThomsonCompact.Cells.base_A_01.W0Sum

/-! W0 sum leaf of cell base_A_01: coordinates 75-99. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_A_01.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.Cells.C_base_A_01.W0

theorem lsum_75_100 : sumOk sumData 12 75 100 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_base_A_01.W0.Leaves
