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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle006
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle007
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle008
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle009
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle010
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle011
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle012

/-! Old `FixedTables.D18` rows 6–12 (`h006`–`h012`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 6–12. -/
noncomputable def oldG1 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 6 then Blueprint.CAP.FixedTables.D18.h006 else
  bif Nat.beq k 7 then Blueprint.CAP.FixedTables.D18.h007 else
  bif Nat.beq k 8 then Blueprint.CAP.FixedTables.D18.h008 else
  bif Nat.beq k 9 then Blueprint.CAP.FixedTables.D18.h009 else
  bif Nat.beq k 10 then Blueprint.CAP.FixedTables.D18.h010 else
  bif Nat.beq k 11 then Blueprint.CAP.FixedTables.D18.h011 else
  bif Nat.beq k 12 then Blueprint.CAP.FixedTables.D18.h012 else
  fun _ => []

theorem oldRows1 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG1 k ⟨m, h⟩ else []) 7 6 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
