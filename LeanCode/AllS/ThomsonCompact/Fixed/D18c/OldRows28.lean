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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle250
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle251
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle252
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle253
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle254
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle255
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle256
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle257
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle258
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle259
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle260
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle261

/-! Old `FixedTables.D18` rows 250–261 (`h250`–`h261`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 250–261. -/
noncomputable def oldG28 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 250 then Blueprint.CAP.FixedTables.D18.h250 else
  bif Nat.beq k 251 then Blueprint.CAP.FixedTables.D18.h251 else
  bif Nat.beq k 252 then Blueprint.CAP.FixedTables.D18.h252 else
  bif Nat.beq k 253 then Blueprint.CAP.FixedTables.D18.h253 else
  bif Nat.beq k 254 then Blueprint.CAP.FixedTables.D18.h254 else
  bif Nat.beq k 255 then Blueprint.CAP.FixedTables.D18.h255 else
  bif Nat.beq k 256 then Blueprint.CAP.FixedTables.D18.h256 else
  bif Nat.beq k 257 then Blueprint.CAP.FixedTables.D18.h257 else
  bif Nat.beq k 258 then Blueprint.CAP.FixedTables.D18.h258 else
  bif Nat.beq k 259 then Blueprint.CAP.FixedTables.D18.h259 else
  bif Nat.beq k 260 then Blueprint.CAP.FixedTables.D18.h260 else
  bif Nat.beq k 261 then Blueprint.CAP.FixedTables.D18.h261 else
  fun _ => []

theorem oldRows28 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG28 k ⟨m, h⟩ else []) 12 250 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
