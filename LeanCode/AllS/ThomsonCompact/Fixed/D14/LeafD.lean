import ThomsonCompact.Fixed.D14.STable

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D14

/-- `Δc_k = S_r S_c rden_b` and the denominator cofactor identities. -/
theorem dc_ok : (dcOk gtab ltab stab 145 && denOk 448 gtab stab) = true := by decide +kernel

end ThomsonCompact.Fixed.D14
