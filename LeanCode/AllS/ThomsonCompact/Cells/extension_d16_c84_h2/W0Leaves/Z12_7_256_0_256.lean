import ThomsonCompact.CoeffMap.Deg.GramN
import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.Shift
import ThomsonCompact.CoeffMap.Deg.D16.RFS
import ThomsonCompact.CoeffMap.Deg.StageZ
import ThomsonCompact.CoeffMap.Deg.GramR
import ThomsonCompact.CoeffMap.Deg.D16.Data
import ThomsonCompact.Cells.extension_d16_c84_h2.W0Ctx
import ThomsonCompact.Cells.extension_d16_c84_h2.W0Z

/-! Stage-Z leaf of cell extension_d16_c84_h2: block 12, dense rows 7-255, rows 0-255 (`CoeffMap/Deg/gen/cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_extension_d16_c84_h2.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_extension_d16_c84_h2.W0

theorem zleaf_12_7_256_0_256 : D16.L.zStageOkC D16.LS 17 6 ctx A (WTn fdata ctx 12) zData 12 7 256 0 256 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_extension_d16_c84_h2.W0.Leaves
