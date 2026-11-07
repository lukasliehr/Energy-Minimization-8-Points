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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle214
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle215
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle216
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle217
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle218
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle219
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle220
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle221
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle222
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle223
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle224
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle225

/-! Old `FixedTables.D18` rows 214–225 (`h214`–`h225`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 214–225. -/
noncomputable def oldG25 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 214 then Blueprint.CAP.FixedTables.D18.h214 else
  bif Nat.beq k 215 then Blueprint.CAP.FixedTables.D18.h215 else
  bif Nat.beq k 216 then Blueprint.CAP.FixedTables.D18.h216 else
  bif Nat.beq k 217 then Blueprint.CAP.FixedTables.D18.h217 else
  bif Nat.beq k 218 then Blueprint.CAP.FixedTables.D18.h218 else
  bif Nat.beq k 219 then Blueprint.CAP.FixedTables.D18.h219 else
  bif Nat.beq k 220 then Blueprint.CAP.FixedTables.D18.h220 else
  bif Nat.beq k 221 then Blueprint.CAP.FixedTables.D18.h221 else
  bif Nat.beq k 222 then Blueprint.CAP.FixedTables.D18.h222 else
  bif Nat.beq k 223 then Blueprint.CAP.FixedTables.D18.h223 else
  bif Nat.beq k 224 then Blueprint.CAP.FixedTables.D18.h224 else
  bif Nat.beq k 225 then Blueprint.CAP.FixedTables.D18.h225 else
  fun _ => []

theorem oldRows25 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG25 k ⟨m, h⟩ else []) 12 214 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
