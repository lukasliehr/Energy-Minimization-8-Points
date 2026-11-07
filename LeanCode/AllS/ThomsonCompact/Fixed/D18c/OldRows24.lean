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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle202
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle203
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle204
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle205
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle206
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle207
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle208
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle209
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle210
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle211
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle212
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle213

/-! Old `FixedTables.D18` rows 202–213 (`h202`–`h213`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 202–213. -/
noncomputable def oldG24 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 202 then Blueprint.CAP.FixedTables.D18.h202 else
  bif Nat.beq k 203 then Blueprint.CAP.FixedTables.D18.h203 else
  bif Nat.beq k 204 then Blueprint.CAP.FixedTables.D18.h204 else
  bif Nat.beq k 205 then Blueprint.CAP.FixedTables.D18.h205 else
  bif Nat.beq k 206 then Blueprint.CAP.FixedTables.D18.h206 else
  bif Nat.beq k 207 then Blueprint.CAP.FixedTables.D18.h207 else
  bif Nat.beq k 208 then Blueprint.CAP.FixedTables.D18.h208 else
  bif Nat.beq k 209 then Blueprint.CAP.FixedTables.D18.h209 else
  bif Nat.beq k 210 then Blueprint.CAP.FixedTables.D18.h210 else
  bif Nat.beq k 211 then Blueprint.CAP.FixedTables.D18.h211 else
  bif Nat.beq k 212 then Blueprint.CAP.FixedTables.D18.h212 else
  bif Nat.beq k 213 then Blueprint.CAP.FixedTables.D18.h213 else
  fun _ => []

theorem oldRows24 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG24 k ⟨m, h⟩ else []) 12 202 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
