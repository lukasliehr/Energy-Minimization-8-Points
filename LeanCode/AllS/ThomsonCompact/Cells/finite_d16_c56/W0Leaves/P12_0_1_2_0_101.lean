import ThomsonCompact.CoeffMap.Deg.GramN
import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.Shift
import ThomsonCompact.CoeffMap.Deg.D16.RFS
import ThomsonCompact.CoeffMap.Deg.StageZ
import ThomsonCompact.CoeffMap.Deg.GramR
import ThomsonCompact.CoeffMap.Deg.D16.Data
import ThomsonCompact.Cells.finite_d16_c56.W0Ctx
import ThomsonCompact.Cells.finite_d16_c56.W0Sum
import ThomsonCompact.Cells.finite_d16_c56.W0Z

/-! Stage-P W0 leaf of cell finite_d16_c56: block 12, groups 0-0, owner part 2, coordinates 0-100 (`CoeffMap/Deg/gen/cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_finite_d16_c56.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_finite_d16_c56.W0

theorem pleaf_12_0_1_2_0_101 : D16.L.leafOk ctx (D16.L.PSC D16.LS 17 6 ctx A (WTt fdata ctx 12) zData 12) sumData 25 12 0 1 2 0 101 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_finite_d16_c56.W0.Leaves
