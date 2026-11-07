import ThomsonCompact.CoeffMap.GramPack
import ThomsonCompact.CoeffMap.BSum
import ThomsonCompact.Cells.base_B_21.W0Ctx
import ThomsonCompact.Cells.base_B_21.W0Sum

/-! W0 leaf of cell base_B_21: block 9, pieces 5-5, coordinates 0-99 (`CoeffMap/gen/w0_cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_B_21.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.Cells.C_base_B_21.W0

theorem leaf_09_5_6_0_100 : blockOkS ctx A (WTp data ctx 9) sumData 16 9 5 6 0 100 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_base_B_21.W0.Leaves
