import ThomsonCompact.TailC.Boundary.Kernel

/-! The boundary SOS kernel leaf (workstream TC1). -/

namespace ThomsonCompact.TailC.Boundary

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem checkAll_true : checkAll = true := by decide +kernel

end ThomsonCompact.TailC.Boundary
