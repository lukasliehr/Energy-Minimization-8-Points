import ThomsonCompact.CoeffMap.BSum
import ThomsonCompact.Cells.base_C_00.W0Sum

/-! W0 sum leaf of cell base_C_00: coordinates 25-36. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_C_00.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.Cells.C_base_C_00.W0

theorem lsum_25_37 : sumOk sumData 27 25 37 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_base_C_00.W0.Leaves
