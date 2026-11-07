import ThomsonCompact.CoeffMap.Deg.Shift
import ThomsonCompact.CoeffMap.Deg.D16.RFS

/-! One-time leaf (F2i): the re-centred D16 shared denominators are the exact shifts of `L`. -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace ThomsonCompact.CoeffMap.Deg.OneTime.D16
open ThomsonCompact.CoeffMap.Deg

theorem shiftDen : D16.L.denShiftAll D16.LS 17 6 = true := by
  decide +kernel

end ThomsonCompact.CoeffMap.Deg.OneTime.D16
