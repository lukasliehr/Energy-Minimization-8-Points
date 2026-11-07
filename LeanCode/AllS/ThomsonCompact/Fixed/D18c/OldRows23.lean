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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle190
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle191
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle192
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle193
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle194
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle195
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle196
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle197
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle198
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle199
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle200
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle201

/-! Old `FixedTables.D18` rows 190–201 (`h190`–`h201`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 190–201. -/
noncomputable def oldG23 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 190 then Blueprint.CAP.FixedTables.D18.h190 else
  bif Nat.beq k 191 then Blueprint.CAP.FixedTables.D18.h191 else
  bif Nat.beq k 192 then Blueprint.CAP.FixedTables.D18.h192 else
  bif Nat.beq k 193 then Blueprint.CAP.FixedTables.D18.h193 else
  bif Nat.beq k 194 then Blueprint.CAP.FixedTables.D18.h194 else
  bif Nat.beq k 195 then Blueprint.CAP.FixedTables.D18.h195 else
  bif Nat.beq k 196 then Blueprint.CAP.FixedTables.D18.h196 else
  bif Nat.beq k 197 then Blueprint.CAP.FixedTables.D18.h197 else
  bif Nat.beq k 198 then Blueprint.CAP.FixedTables.D18.h198 else
  bif Nat.beq k 199 then Blueprint.CAP.FixedTables.D18.h199 else
  bif Nat.beq k 200 then Blueprint.CAP.FixedTables.D18.h200 else
  bif Nat.beq k 201 then Blueprint.CAP.FixedTables.D18.h201 else
  fun _ => []

theorem oldRows23 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG23 k ⟨m, h⟩ else []) 12 190 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
