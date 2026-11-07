import ThomsonCompact.Fixed.D12c.OldKernel
import ThomsonCompact.Fixed.D18c.Slice0
import ThomsonCompact.Fixed.D18c.Slice1
import ThomsonCompact.Fixed.D18c.Slice2
import ThomsonCompact.Fixed.D18c.Slice3
import ThomsonCompact.Fixed.D18c.Slice4
import ThomsonCompact.Fixed.D18c.Slice5
import ThomsonCompact.Fixed.D18c.Slice6
import ThomsonCompact.Fixed.D18c.Slice7
import ThomsonCompact.Fixed.D18c.Slice8
import ThomsonCompact.Fixed.D18c.Slice9
import ThomsonCompact.Fixed.D18c.Slice10
import ThomsonCompact.Fixed.D18c.Slice11
import ThomsonCompact.Fixed.D18c.Slice12
import ThomsonCompact.Fixed.D18c.Slice13
import ThomsonCompact.Fixed.D18c.Slice14
import ThomsonCompact.Fixed.D18c.Slice15
import ThomsonCompact.Fixed.D18c.Slice16
import ThomsonCompact.Fixed.D18c.Slice17
import ThomsonCompact.Fixed.D18c.Slice18
import ThomsonCompact.Fixed.D18c.Slice19
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle023
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle024
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle025
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle026

/-! Old `FixedTables.D18` rows 23–26 (`h023`–`h026`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 23–26. -/
noncomputable def oldG5 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 23 then Blueprint.CAP.FixedTables.D18.h023 else
  bif Nat.beq k 24 then Blueprint.CAP.FixedTables.D18.h024 else
  bif Nat.beq k 25 then Blueprint.CAP.FixedTables.D18.h025 else
  bif Nat.beq k 26 then Blueprint.CAP.FixedTables.D18.h026 else
  fun _ => []

theorem oldRows5 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG5 k ⟨m, h⟩ else []) 4 23 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
