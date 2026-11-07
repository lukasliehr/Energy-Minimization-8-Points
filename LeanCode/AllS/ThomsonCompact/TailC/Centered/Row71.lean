import ThomsonCompact.TailC.Centered.Defs

/-! Centered-quadratic row leaf `(7, 1)` (one-time; workstream TC1). -/

namespace ThomsonCompact.TailC.Centered

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rowOk_7_1 : rowOk (7, 1) := by decide +kernel

end ThomsonCompact.TailC.Centered
