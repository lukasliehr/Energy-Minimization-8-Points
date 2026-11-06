import ThomsonCompact.Fixed.D12c.Tab
import ThomsonCompact.Fixed.D12c.GTable
import ThomsonCompact.Fixed.D12c.LTable
import ThomsonCompact.Fixed.D12c.STable

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D12c

/-- One-time header checks of the stored columns `N` and of `Γ`. -/
theorem tab_ok : tabOk tab = true := by decide +kernel

/-- The Γ/Q link of D12 (stored Γ(B), sQ(B) and the identity Γ_k Δ_k λ_k dz_k = s dq_k Q at the radix). -/
theorem g_ok : gLinkOk tab gtab = true := by decide +kernel

/-- Headers of the κ columns (`L ≤ 13`, `w ≤ 23`, raw rows `< 64`) and output blocks `< 4`. -/
theorem kap_ok : kapHdrOk ltab 100 13 23 64 = true := by decide +kernel

/-- Retained tag codes: pairwise distinct, none flagged non-retained. -/
theorem rtag_ok : rtagOk ltab 100 = true := by decide +kernel

/-- `Δc_k = S_r S_c rden_b` and the denominator cofactor identities. -/
theorem dc_ok : (dcOk gtab ltab stab 100 && denOk 448 gtab stab) = true := by decide +kernel

/-- The m0Plus κ entries are their RF records times δ_b. -/
theorem rf2_ok : rfOk 448 gtab ltab stab 13 23 2 = true := by decide +kernel

/-- The m0Standard κ entries are their RF records times δ_b. -/
theorem rf3_ok : rfOk 448 gtab ltab stab 13 23 3 = true := by decide +kernel

/-- The factorization of Q. -/
theorem fac_ok : facOk 448 gtab stab = true := by decide +kernel

end ThomsonCompact.Fixed.D12c
