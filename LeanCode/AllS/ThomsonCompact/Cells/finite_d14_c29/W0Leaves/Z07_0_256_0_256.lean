import ThomsonCompact.CoeffMap.Deg.GramN
import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.StageZ
import ThomsonCompact.CoeffMap.Deg.D14.Data
import ThomsonCompact.Cells.finite_d14_c29.W0Ctx
import ThomsonCompact.Cells.finite_d14_c29.W0Z

/-! Stage-Z leaf of cell finite_d14_c29: block 7, dense rows 0-255, rows 0-255 (`CoeffMap/Deg/gen/cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_finite_d14_c29.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_finite_d14_c29.W0

theorem zleaf_07_0_256_0_256 : D14.L.zStageOk ctx A (WTn fdata ctx 7) zData 7 0 256 0 256 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_finite_d14_c29.W0.Leaves
