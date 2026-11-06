import ThomsonCompact.Fixed.D16.GTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- The Γ/Q link of D16 (stored Γ(B), sQ(B) and the identity Γ_k Δ_k λ_k dz_k = s dq_k Q at the radix). -/
theorem g_ok : gLinkOk tab gtab = true := by decide +kernel

end ThomsonCompact.Fixed.D16
