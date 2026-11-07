import ThomsonCompact.CoeffMap.BSum
import ThomsonCompact.Cells.base_B_04.W0Sum

/-! W0 sum leaf of cell base_B_04: coordinates 83-99. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_B_04.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.Cells.C_base_B_04.W0

theorem lsum_83_100 : sumOk sumData 21 83 100 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_base_B_04.W0.Leaves
