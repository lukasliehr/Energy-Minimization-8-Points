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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle262
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle263
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle264
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle265
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle266
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle267
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle268
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle269
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle270

/-! Old `FixedTables.D18` rows 262–270 (`h262`–`h270`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 262–270. -/
noncomputable def oldG29 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 262 then Blueprint.CAP.FixedTables.D18.h262 else
  bif Nat.beq k 263 then Blueprint.CAP.FixedTables.D18.h263 else
  bif Nat.beq k 264 then Blueprint.CAP.FixedTables.D18.h264 else
  bif Nat.beq k 265 then Blueprint.CAP.FixedTables.D18.h265 else
  bif Nat.beq k 266 then Blueprint.CAP.FixedTables.D18.h266 else
  bif Nat.beq k 267 then Blueprint.CAP.FixedTables.D18.h267 else
  bif Nat.beq k 268 then Blueprint.CAP.FixedTables.D18.h268 else
  bif Nat.beq k 269 then Blueprint.CAP.FixedTables.D18.h269 else
  bif Nat.beq k 270 then Blueprint.CAP.FixedTables.D18.h270 else
  fun _ => []

theorem oldRows29 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG29 k ⟨m, h⟩ else []) 9 262 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
