import ThomsonCompact.CoeffMap.GramPack
import ThomsonCompact.CoeffMap.BSum
import ThomsonCompact.Cells.base_B_26.W0Ctx
import ThomsonCompact.Cells.base_B_26.W0Sum

/-! W0 leaf of cell base_B_26: block 9, pieces 6-6, coordinates 50-99 (`CoeffMap/gen/w0_cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_B_26.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.Cells.C_base_B_26.W0

theorem leaf_09_6_7_50_100 : blockOkS ctx A (WTp data ctx 9) sumData 16 9 6 7 50 100 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_base_B_26.W0.Leaves
