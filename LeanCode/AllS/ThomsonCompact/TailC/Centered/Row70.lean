import ThomsonCompact.TailC.Centered.Defs

/-! Centered-quadratic row leaf `(7, 0)` (one-time; workstream TC1). -/

namespace ThomsonCompact.TailC.Centered

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rowOk_7_0 : rowOk (7, 0) := by decide +kernel

end ThomsonCompact.TailC.Centered
