import ThomsonCompact.CoeffMap.BSum
import ThomsonCompact.Cells.base_A_05.W0Sum

/-! W0 sum leaf of cell base_A_05: coordinates 16-32. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_A_05.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.Cells.C_base_A_05.W0

theorem lsum_16_33 : sumOk sumData 17 16 33 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_base_A_05.W0.Leaves
