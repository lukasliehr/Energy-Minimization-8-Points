import ThomsonCompact.CoeffMap.Deg.GramN
import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.Shift
import ThomsonCompact.CoeffMap.Deg.D16.RFS
import ThomsonCompact.CoeffMap.Deg.StageZ
import ThomsonCompact.CoeffMap.Deg.GramR
import ThomsonCompact.CoeffMap.Deg.D16.Data
import ThomsonCompact.Cells.finite_d16_c56.W0Ctx
import ThomsonCompact.Cells.finite_d16_c56.W0Z

/-! Stage-Z leaf of cell finite_d16_c56: block 8, dense rows 4-255, rows 0-255 (`CoeffMap/Deg/gen/cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_finite_d16_c56.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_finite_d16_c56.W0

theorem zleaf_08_4_256_0_256 : D16.L.zStageOkC D16.LS 17 6 ctx A (WTn fdata ctx 8) zData 8 4 256 0 256 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_finite_d16_c56.W0.Leaves
