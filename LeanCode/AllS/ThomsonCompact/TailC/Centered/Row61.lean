import ThomsonCompact.TailC.Centered.Defs

/-! Centered-quadratic row leaf `(6, 1)` (one-time; workstream TC1). -/

namespace ThomsonCompact.TailC.Centered

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rowOk_6_1 : rowOk (6, 1) := by decide +kernel

end ThomsonCompact.TailC.Centered
