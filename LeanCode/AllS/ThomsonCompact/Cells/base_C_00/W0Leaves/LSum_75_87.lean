import ThomsonCompact.CoeffMap.BSum
import ThomsonCompact.Cells.base_C_00.W0Sum

/-! W0 sum leaf of cell base_C_00: coordinates 75-86. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_C_00.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.Cells.C_base_C_00.W0

theorem lsum_75_87 : sumOk sumData 27 75 87 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_base_C_00.W0.Leaves
