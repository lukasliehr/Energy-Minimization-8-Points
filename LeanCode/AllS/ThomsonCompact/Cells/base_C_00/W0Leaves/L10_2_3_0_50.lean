import ThomsonCompact.CoeffMap.GramPack
import ThomsonCompact.CoeffMap.BSum
import ThomsonCompact.Cells.base_C_00.W0Ctx
import ThomsonCompact.Cells.base_C_00.W0Sum

/-! W0 leaf of cell base_C_00: block 10, pieces 2-2, coordinates 0-49 (`CoeffMap/gen/w0_cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_C_00.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.Cells.C_base_C_00.W0

theorem leaf_10_2_3_0_50 : blockOkS ctx A (WTp data ctx 10) sumData 27 10 2 3 0 50 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_base_C_00.W0.Leaves
