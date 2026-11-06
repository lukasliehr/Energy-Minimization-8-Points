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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle118
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle119
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle120
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle121
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle122
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle123
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle124
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle125
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle126
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle127
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle128
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle129

/-! Old `FixedTables.D18` rows 118–129 (`h118`–`h129`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 118–129. -/
noncomputable def oldG17 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 118 then Blueprint.CAP.FixedTables.D18.h118 else
  bif Nat.beq k 119 then Blueprint.CAP.FixedTables.D18.h119 else
  bif Nat.beq k 120 then Blueprint.CAP.FixedTables.D18.h120 else
  bif Nat.beq k 121 then Blueprint.CAP.FixedTables.D18.h121 else
  bif Nat.beq k 122 then Blueprint.CAP.FixedTables.D18.h122 else
  bif Nat.beq k 123 then Blueprint.CAP.FixedTables.D18.h123 else
  bif Nat.beq k 124 then Blueprint.CAP.FixedTables.D18.h124 else
  bif Nat.beq k 125 then Blueprint.CAP.FixedTables.D18.h125 else
  bif Nat.beq k 126 then Blueprint.CAP.FixedTables.D18.h126 else
  bif Nat.beq k 127 then Blueprint.CAP.FixedTables.D18.h127 else
  bif Nat.beq k 128 then Blueprint.CAP.FixedTables.D18.h128 else
  bif Nat.beq k 129 then Blueprint.CAP.FixedTables.D18.h129 else
  fun _ => []

theorem oldRows17 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG17 k ⟨m, h⟩ else []) 12 118 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
