import ThomsonCompact.CoeffMap.Deg.GramN
import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.Shift
import ThomsonCompact.CoeffMap.Deg.D16.RFS
import ThomsonCompact.CoeffMap.Deg.StageZ
import ThomsonCompact.CoeffMap.Deg.GramR
import ThomsonCompact.CoeffMap.Deg.D16.Data
import ThomsonCompact.Cells.finite_d16_c68.W0Ctx
import ThomsonCompact.Cells.finite_d16_c68.W0Z

/-! Stage-Z leaf of cell finite_d16_c68: block 10, dense rows 5-31, rows 0-255 (`CoeffMap/Deg/gen/cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_finite_d16_c68.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_finite_d16_c68.W0

theorem zleaf_10_5_32_0_256 : D16.L.zStageOkC D16.LS 17 6 ctx A (WTn fdata ctx 10) zData 10 5 32 0 256 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_finite_d16_c68.W0.Leaves
