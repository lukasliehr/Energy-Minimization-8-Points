import ThomsonCompact.CoeffMap.GramPack
import ThomsonCompact.CoeffMap.BSum
import ThomsonCompact.Cells.base_B_41.W0Ctx
import ThomsonCompact.Cells.base_B_41.W0Sum

/-! W0 leaf of cell base_B_41: block 9, pieces 4-4, coordinates 0-49 (`CoeffMap/gen/w0_cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_B_41.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.Cells.C_base_B_41.W0

theorem leaf_09_4_5_0_50 : blockOkS ctx A (WTp data ctx 9) sumData 16 9 4 5 0 50 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_base_B_41.W0.Leaves
