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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle039
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle040
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle041
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle042
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle043
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle044
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle045

/-! Old `FixedTables.D18` rows 39–45 (`h039`–`h045`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 39–45. -/
noncomputable def oldG10 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 39 then Blueprint.CAP.FixedTables.D18.h039 else
  bif Nat.beq k 40 then Blueprint.CAP.FixedTables.D18.h040 else
  bif Nat.beq k 41 then Blueprint.CAP.FixedTables.D18.h041 else
  bif Nat.beq k 42 then Blueprint.CAP.FixedTables.D18.h042 else
  bif Nat.beq k 43 then Blueprint.CAP.FixedTables.D18.h043 else
  bif Nat.beq k 44 then Blueprint.CAP.FixedTables.D18.h044 else
  bif Nat.beq k 45 then Blueprint.CAP.FixedTables.D18.h045 else
  fun _ => []

theorem oldRows10 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG10 k ⟨m, h⟩ else []) 7 39 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
