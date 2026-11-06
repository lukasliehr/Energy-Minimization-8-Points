import ThomsonCompact.CoeffMap.Deg.GramN
import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.Shift
import ThomsonCompact.CoeffMap.Deg.D16.RFS
import ThomsonCompact.CoeffMap.Deg.D16.Data
import ThomsonCompact.Cells.finite_d16_c68.W0Ctx
import ThomsonCompact.Cells.finite_d16_c68.W0Sum

/-! W0 leaf of cell finite_d16_c68: block 14, groups 0-0, owner part 0, coordinates 0-201 (`CoeffMap/Deg/gen/cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_finite_d16_c68.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_finite_d16_c68.W0

theorem leaf_14_0_1_0_0_202 : D16.L.leafOk ctx (D16.L.pLookC D16.LS 17 6 ctx A (WTn fdata ctx 14) 14) sumData 30 14 0 1 0 0 202 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_finite_d16_c68.W0.Leaves
