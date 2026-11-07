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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle058
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle059
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle060
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle061
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle062
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle063
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle064
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle065
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle066
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle067
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle068
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle069

/-! Old `FixedTables.D18` rows 58–69 (`h058`–`h069`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 58–69. -/
noncomputable def oldG12 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 58 then Blueprint.CAP.FixedTables.D18.h058 else
  bif Nat.beq k 59 then Blueprint.CAP.FixedTables.D18.h059 else
  bif Nat.beq k 60 then Blueprint.CAP.FixedTables.D18.h060 else
  bif Nat.beq k 61 then Blueprint.CAP.FixedTables.D18.h061 else
  bif Nat.beq k 62 then Blueprint.CAP.FixedTables.D18.h062 else
  bif Nat.beq k 63 then Blueprint.CAP.FixedTables.D18.h063 else
  bif Nat.beq k 64 then Blueprint.CAP.FixedTables.D18.h064 else
  bif Nat.beq k 65 then Blueprint.CAP.FixedTables.D18.h065 else
  bif Nat.beq k 66 then Blueprint.CAP.FixedTables.D18.h066 else
  bif Nat.beq k 67 then Blueprint.CAP.FixedTables.D18.h067 else
  bif Nat.beq k 68 then Blueprint.CAP.FixedTables.D18.h068 else
  bif Nat.beq k 69 then Blueprint.CAP.FixedTables.D18.h069 else
  fun _ => []

theorem oldRows12 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG12 k ⟨m, h⟩ else []) 12 58 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
