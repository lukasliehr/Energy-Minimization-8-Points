import ThomsonCompact.CoeffMap.Deg.GramN
import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.StageZ
import ThomsonCompact.CoeffMap.Deg.D14.Data
import ThomsonCompact.Cells.finite_d14_c41.W0Ctx
import ThomsonCompact.Cells.finite_d14_c41.W0Z

/-! Stage-Z leaf of cell finite_d14_c41: block 9, dense rows 7-255, rows 0-255 (`CoeffMap/Deg/gen/cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_finite_d14_c41.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_finite_d14_c41.W0

theorem zleaf_09_7_256_0_256 : D14.L.zStageOk ctx A (WTn fdata ctx 9) zData 9 7 256 0 256 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_finite_d14_c41.W0.Leaves
