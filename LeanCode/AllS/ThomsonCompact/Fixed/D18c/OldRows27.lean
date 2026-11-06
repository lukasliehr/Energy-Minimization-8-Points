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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle238
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle239
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle240
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle241
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle242
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle243
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle244
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle245
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle246
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle247
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle248
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle249

/-! Old `FixedTables.D18` rows 238–249 (`h238`–`h249`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 238–249. -/
noncomputable def oldG27 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 238 then Blueprint.CAP.FixedTables.D18.h238 else
  bif Nat.beq k 239 then Blueprint.CAP.FixedTables.D18.h239 else
  bif Nat.beq k 240 then Blueprint.CAP.FixedTables.D18.h240 else
  bif Nat.beq k 241 then Blueprint.CAP.FixedTables.D18.h241 else
  bif Nat.beq k 242 then Blueprint.CAP.FixedTables.D18.h242 else
  bif Nat.beq k 243 then Blueprint.CAP.FixedTables.D18.h243 else
  bif Nat.beq k 244 then Blueprint.CAP.FixedTables.D18.h244 else
  bif Nat.beq k 245 then Blueprint.CAP.FixedTables.D18.h245 else
  bif Nat.beq k 246 then Blueprint.CAP.FixedTables.D18.h246 else
  bif Nat.beq k 247 then Blueprint.CAP.FixedTables.D18.h247 else
  bif Nat.beq k 248 then Blueprint.CAP.FixedTables.D18.h248 else
  bif Nat.beq k 249 then Blueprint.CAP.FixedTables.D18.h249 else
  fun _ => []

theorem oldRows27 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG27 k ⟨m, h⟩ else []) 12 238 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
