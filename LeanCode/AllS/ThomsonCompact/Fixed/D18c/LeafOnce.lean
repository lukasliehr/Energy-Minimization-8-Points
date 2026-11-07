import ThomsonCompact.Fixed.D18c.Tab
import ThomsonCompact.Fixed.D18c.GTable
import ThomsonCompact.Fixed.D18c.LTable
import ThomsonCompact.Fixed.D18c.STable

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

/-- One-time header checks of the stored columns `N` and of `Γ`. -/
theorem tab_ok : tabOk tab = true := by decide +kernel

/-- The Γ/Q link of D18 (stored Γ(B), sQ(B) and the identity Γ_k Δ_k λ_k dz_k = s dq_k Q at the radix). -/
theorem g_ok : gLinkOk tab gtab = true := by decide +kernel

/-- Headers of the κ columns (`L ≤ 16`, `w ≤ 26`, raw rows `< 128`) and output blocks `< 4`. -/
theorem kap_ok : kapHdrOk ltab 272 16 26 128 = true := by decide +kernel

/-- Retained tag codes: pairwise distinct, none flagged non-retained. -/
theorem rtag_ok : rtagOk ltab 272 = true := by decide +kernel

/-- `Δc_k = S_r S_c rden_b` and the denominator cofactor identities. -/
theorem dc_ok : (dcOk gtab ltab stab 272 && denOk 448 gtab stab) = true := by decide +kernel

/-- The m0Plus κ entries are their RF records times δ_b. -/
theorem rf2_ok : rfOk 448 gtab ltab stab 16 26 2 = true := by decide +kernel

/-- The m0Standard κ entries are their RF records times δ_b. -/
theorem rf3_ok : rfOk 448 gtab ltab stab 16 26 3 = true := by decide +kernel

/-- The factorization of Q. -/
theorem fac_ok : facOk 448 gtab stab = true := by decide +kernel

end ThomsonCompact.Fixed.D18c
