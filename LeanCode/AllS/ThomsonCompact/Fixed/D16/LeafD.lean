import ThomsonCompact.Fixed.D16.STable

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D16

/-- `Δc_k = S_r S_c rden_b` and the denominator cofactor identities. -/
theorem dc_ok : (dcOk gtab ltab stab 202 && denOk 448 gtab stab) = true := by decide +kernel

end ThomsonCompact.Fixed.D16
