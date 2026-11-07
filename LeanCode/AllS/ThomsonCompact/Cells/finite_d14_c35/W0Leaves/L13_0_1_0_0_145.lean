import ThomsonCompact.CoeffMap.Deg.GramN
import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.D14.Data
import ThomsonCompact.Cells.finite_d14_c35.W0Ctx
import ThomsonCompact.Cells.finite_d14_c35.W0Sum

/-! W0 leaf of cell finite_d14_c35: block 13, groups 0-0, owner part 0, coordinates 0-144 (`CoeffMap/Deg/gen/cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_finite_d14_c35.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_finite_d14_c35.W0

theorem leaf_13_0_1_0_0_145 : D14.L.leafOk ctx (D14.L.pLook ctx A (WTn fdata ctx 13) 13) sumData 27 13 0 1 0 0 145 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_finite_d14_c35.W0.Leaves
