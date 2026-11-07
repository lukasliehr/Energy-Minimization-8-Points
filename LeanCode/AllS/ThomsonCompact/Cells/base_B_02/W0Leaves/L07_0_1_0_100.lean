import ThomsonCompact.CoeffMap.GramPack
import ThomsonCompact.CoeffMap.BSum
import ThomsonCompact.Cells.base_B_02.W0Ctx
import ThomsonCompact.Cells.base_B_02.W0Sum

/-! W0 leaf of cell base_B_02: block 7, pieces 0-0, coordinates 0-99 (`CoeffMap/gen/w0_cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_B_02.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.Cells.C_base_B_02.W0

theorem leaf_07_0_1_0_100 : blockOkS ctx A (WTp data ctx 7) sumData 13 7 0 1 0 100 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_base_B_02.W0.Leaves
