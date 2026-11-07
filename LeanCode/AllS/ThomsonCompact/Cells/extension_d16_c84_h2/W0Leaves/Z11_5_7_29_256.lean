import ThomsonCompact.CoeffMap.Deg.GramN
import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.Shift
import ThomsonCompact.CoeffMap.Deg.D16.RFS
import ThomsonCompact.CoeffMap.Deg.StageZ
import ThomsonCompact.CoeffMap.Deg.GramR
import ThomsonCompact.CoeffMap.Deg.D16.Data
import ThomsonCompact.Cells.extension_d16_c84_h2.W0Ctx
import ThomsonCompact.Cells.extension_d16_c84_h2.W0Z

/-! Stage-Z leaf of cell extension_d16_c84_h2: block 11, dense rows 5-6, rows 29-255 (`CoeffMap/Deg/gen/cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_extension_d16_c84_h2.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_extension_d16_c84_h2.W0

theorem zleaf_11_5_7_29_256 : D16.L.zStageOkC D16.LS 17 6 ctx A (WTr fdata ctx 11) zData 11 5 7 29 256 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_extension_d16_c84_h2.W0.Leaves
