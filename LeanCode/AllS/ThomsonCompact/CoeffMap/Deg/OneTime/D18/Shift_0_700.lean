import ThomsonCompact.CoeffMap.Deg.Shift
import ThomsonCompact.CoeffMap.Deg.D18.RFS

/-! One-time leaf (F2i): the re-centred D18 records 0-699 are the exact shifts of `L`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.CoeffMap.Deg.OneTime.D18
open ThomsonCompact.CoeffMap.Deg

theorem shift_0_700 : D18.L.recShiftRange D18.LS 17 6 0 700 = true := by
  decide +kernel

end ThomsonCompact.CoeffMap.Deg.OneTime.D18
