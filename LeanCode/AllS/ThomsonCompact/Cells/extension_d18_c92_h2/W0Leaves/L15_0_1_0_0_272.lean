import ThomsonCompact.CoeffMap.Deg.GramN
import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.Shift
import ThomsonCompact.CoeffMap.Deg.D18.RFS
import ThomsonCompact.CoeffMap.Deg.D18.Data
import ThomsonCompact.Cells.extension_d18_c92_h2.W0Ctx
import ThomsonCompact.Cells.extension_d18_c92_h2.W0Sum

/-! W0 leaf of cell extension_d18_c92_h2: block 15, groups 0-0, owner part 0, coordinates 0-271 (`CoeffMap/Deg/gen/cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_extension_d18_c92_h2.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_extension_d18_c92_h2.W0

theorem leaf_15_0_1_0_0_272 : D18.L.leafOk ctx (D18.L.pLookC D18.LS 17 6 ctx A (WTn fdata ctx 15) 15) sumData 22 15 0 1 0 0 272 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_extension_d18_c92_h2.W0.Leaves
