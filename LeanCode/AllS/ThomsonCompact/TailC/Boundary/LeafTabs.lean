import ThomsonCompact.TailC.Boundary.Tabs

/-! Index-table leaves (workstream TC1). -/

namespace ThomsonCompact.TailC.Boundary

set_option maxHeartbeats 0
set_option maxRecDepth 200000

theorem q2Ok_true : q2Ok = true := by decide +kernel
theorem g1Ok_true : g1Ok = true := by decide +kernel
theorem dOk_true : dOk = true := by decide +kernel
theorem g2Ok_true : g2Ok 0 105 = true := by decide +kernel

end ThomsonCompact.TailC.Boundary
