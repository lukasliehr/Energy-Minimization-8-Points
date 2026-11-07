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

/-! Stage-P W0 leaf of cell finite_d16_c56: block 11, groups 0-0, owner part 5, coordinates 101-201 (`CoeffMap/Deg/gen/cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_finite_d16_c56.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_finite_d16_c56.W0

theorem pleaf_11_0_1_5_101_202 : D16.L.leafOk ctx (D16.L.PSC D16.LS 17 6 ctx A (WTt fdata ctx 11) zData 11) sumData 25 11 0 1 5 101 202 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_finite_d16_c56.W0.Leaves
