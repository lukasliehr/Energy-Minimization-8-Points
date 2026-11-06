import ThomsonCompact.CoeffMap.Deg.GramN
import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.StageZ
import ThomsonCompact.CoeffMap.Deg.D14.Data
import ThomsonCompact.Cells.finite_d14_c23.W0Ctx
import ThomsonCompact.Cells.finite_d14_c23.W0Sum
import ThomsonCompact.Cells.finite_d14_c23.W0Z

/-! Stage-P W0 leaf of cell finite_d14_c23: block 11, groups 0-0, owner part 1, coordinates 0-144 (`CoeffMap/Deg/gen/cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_finite_d14_c23.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_finite_d14_c23.W0

theorem pleaf_11_0_1_1_0_145 : D14.L.leafOk ctx (D14.L.PS ctx A (WTn fdata ctx 11) zData 11) sumData 28 11 0 1 1 0 145 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_finite_d14_c23.W0.Leaves
