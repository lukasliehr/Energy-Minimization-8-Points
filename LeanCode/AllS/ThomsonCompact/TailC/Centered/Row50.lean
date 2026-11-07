import ThomsonCompact.TailC.Centered.Defs

/-! Centered-quadratic row leaf `(5, 0)` (one-time; workstream TC1). -/

namespace ThomsonCompact.TailC.Centered

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rowOk_5_0 : rowOk (5, 0) := by decide +kernel

end ThomsonCompact.TailC.Centered
