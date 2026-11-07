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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle106
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle107
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle108
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle109
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle110
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle111
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle112
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle113
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle114
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle115
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle116
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle117

/-! Old `FixedTables.D18` rows 106–117 (`h106`–`h117`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 106–117. -/
noncomputable def oldG16 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 106 then Blueprint.CAP.FixedTables.D18.h106 else
  bif Nat.beq k 107 then Blueprint.CAP.FixedTables.D18.h107 else
  bif Nat.beq k 108 then Blueprint.CAP.FixedTables.D18.h108 else
  bif Nat.beq k 109 then Blueprint.CAP.FixedTables.D18.h109 else
  bif Nat.beq k 110 then Blueprint.CAP.FixedTables.D18.h110 else
  bif Nat.beq k 111 then Blueprint.CAP.FixedTables.D18.h111 else
  bif Nat.beq k 112 then Blueprint.CAP.FixedTables.D18.h112 else
  bif Nat.beq k 113 then Blueprint.CAP.FixedTables.D18.h113 else
  bif Nat.beq k 114 then Blueprint.CAP.FixedTables.D18.h114 else
  bif Nat.beq k 115 then Blueprint.CAP.FixedTables.D18.h115 else
  bif Nat.beq k 116 then Blueprint.CAP.FixedTables.D18.h116 else
  bif Nat.beq k 117 then Blueprint.CAP.FixedTables.D18.h117 else
  fun _ => []

theorem oldRows16 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG16 k ⟨m, h⟩ else []) 12 106 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
