import ThomsonCompact.CoeffMap.Deg.GramN
import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.StageZ
import ThomsonCompact.CoeffMap.Deg.D14.Data
import ThomsonCompact.Cells.finite_d14_c18.W0Ctx
import ThomsonCompact.Cells.finite_d14_c18.W0Z

/-! Stage-Z leaf of cell finite_d14_c18: block 10, dense rows 0-3, rows 0-255 (`CoeffMap/Deg/gen/cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_finite_d14_c18.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_finite_d14_c18.W0

theorem zleaf_10_0_4_0_256 : D14.L.zStageOk ctx A (WTn fdata ctx 10) zData 10 0 4 0 256 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_finite_d14_c18.W0.Leaves
