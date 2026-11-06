import ThomsonCompact.CoeffMap.GramPack
import ThomsonCompact.CoeffMap.BSum
import ThomsonCompact.Cells.base_B_30.W0Ctx
import ThomsonCompact.Cells.base_B_30.W0Sum

/-! W0 leaf of cell base_B_30: block 8, pieces 1-1, coordinates 50-99 (`CoeffMap/gen/w0_cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_B_30.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.Cells.C_base_B_30.W0

theorem leaf_08_1_2_50_100 : blockOkS ctx A (WTp data ctx 8) sumData 17 8 1 2 50 100 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_base_B_30.W0.Leaves
