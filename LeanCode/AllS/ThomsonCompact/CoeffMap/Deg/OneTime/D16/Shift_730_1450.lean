import ThomsonCompact.CoeffMap.Deg.Shift
import ThomsonCompact.CoeffMap.Deg.D16.RFS

/-! One-time leaf (F2i): the re-centred D16 records 730-1449 are the exact shifts of `L`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.CoeffMap.Deg.OneTime.D16
open ThomsonCompact.CoeffMap.Deg

theorem shift_730_1450 : D16.L.recShiftRange D16.LS 17 6 730 1450 = true := by
  decide +kernel

end ThomsonCompact.CoeffMap.Deg.OneTime.D16
