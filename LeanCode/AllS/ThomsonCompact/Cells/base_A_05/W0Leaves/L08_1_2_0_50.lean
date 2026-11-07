import ThomsonCompact.CoeffMap.GramPack
import ThomsonCompact.CoeffMap.BSum
import ThomsonCompact.Cells.base_A_05.W0Ctx
import ThomsonCompact.Cells.base_A_05.W0Sum

/-! W0 leaf of cell base_A_05: block 8, pieces 1-1, coordinates 0-49 (`CoeffMap/gen/w0_cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_A_05.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.Cells.C_base_A_05.W0

theorem leaf_08_1_2_0_50 : blockOkS ctx A (WTp data ctx 8) sumData 17 8 1 2 0 50 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_base_A_05.W0.Leaves
