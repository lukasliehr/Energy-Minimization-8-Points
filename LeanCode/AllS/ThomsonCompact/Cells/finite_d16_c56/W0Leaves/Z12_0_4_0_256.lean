import ThomsonCompact.CoeffMap.Deg.GramN
import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.Shift
import ThomsonCompact.CoeffMap.Deg.D16.RFS
import ThomsonCompact.CoeffMap.Deg.StageZ
import ThomsonCompact.CoeffMap.Deg.GramR
import ThomsonCompact.CoeffMap.Deg.D16.Data
import ThomsonCompact.Cells.finite_d16_c56.W0Ctx
import ThomsonCompact.Cells.finite_d16_c56.W0Z

/-! Stage-Z leaf of cell finite_d16_c56: block 12, dense rows 0-3, rows 0-255 (`CoeffMap/Deg/gen/cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_finite_d16_c56.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_finite_d16_c56.W0

theorem zleaf_12_0_4_0_256 : D16.L.zStageOkC D16.LS 17 6 ctx A (WTn fdata ctx 12) zData 12 0 4 0 256 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_finite_d16_c56.W0.Leaves
