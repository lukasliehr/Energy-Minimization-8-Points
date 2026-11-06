import ThomsonCompact.Fixed.D12c.OldKernel
import ThomsonCompact.Fixed.D12c.Slice0
import ThomsonCompact.Fixed.D12c.Slice1
import ThomsonCompact.Fixed.D12c.Slice2
import ThomsonCompact.Fixed.D12c.Slice3
import ThomsonCompact.Fixed.D12c.Slice4
import ThomsonCompact.Fixed.D12c.Slice5
import ThomsonCompact.Fixed.D12c.Slice6
import ThomsonCompact.Fixed.D12c.Slice7
import AllS.Units.N_AI.N_fixed_tables.D12.Data

/-! Old `FixedTables.D12.H` rows 20–39 against the compact slices (exact coefficient lists; F4c identification leaf). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D12c

open ThomsonCompact.Fixed

theorem oldRows1 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7]
    (fun k m => if h : k < 100 ∧ m < 100 then Blueprint.CAP.FixedTables.D12.H ⟨k, h.1⟩ ⟨m, h.2⟩ else []) 20 20 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D12c
