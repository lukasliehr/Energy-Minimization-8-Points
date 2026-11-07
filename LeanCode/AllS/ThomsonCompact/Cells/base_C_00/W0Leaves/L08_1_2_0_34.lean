import ThomsonCompact.CoeffMap.GramPack
import ThomsonCompact.CoeffMap.BSum
import ThomsonCompact.Cells.base_C_00.W0Ctx
import ThomsonCompact.Cells.base_C_00.W0Sum

/-! W0 leaf of cell base_C_00: block 8, pieces 1-1, coordinates 0-33 (`CoeffMap/gen/w0_cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_C_00.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.Cells.C_base_C_00.W0

theorem leaf_08_1_2_0_34 : blockOkS ctx A (WTp data ctx 8) sumData 27 8 1 2 0 34 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_base_C_00.W0.Leaves
