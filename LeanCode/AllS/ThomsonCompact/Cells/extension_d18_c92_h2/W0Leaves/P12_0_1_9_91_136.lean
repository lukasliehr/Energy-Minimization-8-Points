import ThomsonCompact.CoeffMap.Deg.GramN
import ThomsonCompact.CoeffMap.Deg.Prog
import ThomsonCompact.CoeffMap.Deg.Shift
import ThomsonCompact.CoeffMap.Deg.D18.RFS
import ThomsonCompact.CoeffMap.Deg.StageZ
import ThomsonCompact.CoeffMap.Deg.GramR
import ThomsonCompact.CoeffMap.Deg.D18.Data
import ThomsonCompact.Cells.extension_d18_c92_h2.W0Ctx
import ThomsonCompact.Cells.extension_d18_c92_h2.W0Sum
import ThomsonCompact.Cells.extension_d18_c92_h2.W0Z

/-! Stage-P W0 leaf of cell extension_d18_c92_h2: block 12, groups 0-0, owner part 9, coordinates 91-135 (`CoeffMap/Deg/gen/cells.py`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.Cells.C_extension_d18_c92_h2.W0.Leaves
open ThomsonCompact.Packed ThomsonCompact.CoeffMap ThomsonCompact.CoeffMap.Deg ThomsonCompact.Cells.C_extension_d18_c92_h2.W0

theorem pleaf_12_0_1_9_91_136 : D18.L.leafOk ctx (D18.L.PSC D18.LS 17 6 ctx A (WTt fdata ctx 12) zData 12) sumData 22 12 0 1 9 91 136 = true := by
  decide +kernel

end ThomsonCompact.Cells.C_extension_d18_c92_h2.W0.Leaves
