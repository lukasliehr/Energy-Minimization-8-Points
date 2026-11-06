import ThomsonCompact.Fixed.D16.Tab

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- One-time header checks of the stored columns `N` and of `Γ`. -/
theorem tab_ok : tabOk tab = true := by decide +kernel

end ThomsonCompact.Fixed.D16
