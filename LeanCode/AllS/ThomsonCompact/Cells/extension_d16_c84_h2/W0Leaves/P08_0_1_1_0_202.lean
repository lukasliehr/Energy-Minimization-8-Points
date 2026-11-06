import ThomsonCompact.CoeffMap.Deg.GramN
import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.Shift
import ThomsonCompact.CoeffMap.Deg.D16.RFS
import ThomsonCompact.CoeffMap.Deg.StageZ
import ThomsonCompact.CoeffMap.Deg.GramR
import ThomsonCompact.CoeffMap.Deg.D16.Data
import ThomsonCompact.Cells.extension_d16_c84_h2.W0Ctx
import ThomsonCompact.Cells.extension_d16_c84_h2.W0Sum
import ThomsonCompact.Cells.extension_d16_c84_h2.W0Z

/-! Stage-P W0 leaf of cell extension_d16_c84_h2: block 8, groups 0-0, owner part 1, coordinates 0-201 (`CoeffMap/Deg/gen/cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_extension_d16_c84_h2.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_extension_d16_c84_h2.W0

theorem pleaf_08_0_1_1_0_202 : D16.L.leafOk ctx (D16.L.PSC D16.LS 17 6 ctx A (WTt fdata ctx 8) zData 8) sumData 18 8 0 1 1 0 202 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_extension_d16_c84_h2.W0.Leaves
