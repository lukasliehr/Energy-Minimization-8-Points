import ThomsonCompact.Fixed.D12c.OldKernel
import ThomsonCompact.Fixed.D12c.GTable
import AllS.Units.N_AI.N_fixed_tables.D12.Data

/-! Old `FixedTables.D12.tableScales`/`tableDenominators` against the compact Γ/Q-link data: `λ_k`, `dz_k/dq_k`
(F4c identification leaf). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D12c

open ThomsonCompact.Fixed

theorem oldDen : (List.range 100).all (fun k => if h : k < 100 then
    decide (Blueprint.CAP.FixedTables.D12.tableScales ⟨k, h⟩ = ((fld (gtab.inf k) 0 128 : ℕ) : ℤ)) &&
    decide (Blueprint.CAP.FixedTables.D12.tableDenominators ⟨k, h⟩ =
      (dzK gtab k).map (fun z : ℤ => (z : ℚ) / ((fld (gtab.inf k) 128 128 : ℕ) : ℚ)))
  else true) = true := by
  decide +kernel

end ThomsonCompact.Fixed.D12c
