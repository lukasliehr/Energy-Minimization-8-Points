import ThomsonCompact.CoeffMap.GramPack
import ThomsonCompact.CoeffMap.BSum
import ThomsonCompact.Cells.base_C_00.W0Ctx
import ThomsonCompact.Cells.base_C_00.W0Sum

/-! W0 leaf of cell base_C_00: block 8, pieces 0-0, coordinates 67-99 (`CoeffMap/gen/w0_cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_base_C_00.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.Cells.C_base_C_00.W0

theorem leaf_08_0_1_67_100 : blockOkS ctx A (WTp data ctx 8) sumData 27 8 0 1 67 100 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_base_C_00.W0.Leaves
