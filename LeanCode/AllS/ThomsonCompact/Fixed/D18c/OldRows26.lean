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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle226
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle227
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle228
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle229
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle230
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle231
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle232
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle233
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle234
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle235
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle236
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle237

/-! Old `FixedTables.D18` rows 226–237 (`h226`–`h237`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 226–237. -/
noncomputable def oldG26 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 226 then Blueprint.CAP.FixedTables.D18.h226 else
  bif Nat.beq k 227 then Blueprint.CAP.FixedTables.D18.h227 else
  bif Nat.beq k 228 then Blueprint.CAP.FixedTables.D18.h228 else
  bif Nat.beq k 229 then Blueprint.CAP.FixedTables.D18.h229 else
  bif Nat.beq k 230 then Blueprint.CAP.FixedTables.D18.h230 else
  bif Nat.beq k 231 then Blueprint.CAP.FixedTables.D18.h231 else
  bif Nat.beq k 232 then Blueprint.CAP.FixedTables.D18.h232 else
  bif Nat.beq k 233 then Blueprint.CAP.FixedTables.D18.h233 else
  bif Nat.beq k 234 then Blueprint.CAP.FixedTables.D18.h234 else
  bif Nat.beq k 235 then Blueprint.CAP.FixedTables.D18.h235 else
  bif Nat.beq k 236 then Blueprint.CAP.FixedTables.D18.h236 else
  bif Nat.beq k 237 then Blueprint.CAP.FixedTables.D18.h237 else
  fun _ => []

theorem oldRows26 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG26 k ⟨m, h⟩ else []) 12 226 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
