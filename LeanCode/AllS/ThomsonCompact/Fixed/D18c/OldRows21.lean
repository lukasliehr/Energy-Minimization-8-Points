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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle166
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle167
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle168
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle169
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle170
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle171
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle172
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle173
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle174
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle175
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle176
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle177

/-! Old `FixedTables.D18` rows 166–177 (`h166`–`h177`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 166–177. -/
noncomputable def oldG21 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 166 then Blueprint.CAP.FixedTables.D18.h166 else
  bif Nat.beq k 167 then Blueprint.CAP.FixedTables.D18.h167 else
  bif Nat.beq k 168 then Blueprint.CAP.FixedTables.D18.h168 else
  bif Nat.beq k 169 then Blueprint.CAP.FixedTables.D18.h169 else
  bif Nat.beq k 170 then Blueprint.CAP.FixedTables.D18.h170 else
  bif Nat.beq k 171 then Blueprint.CAP.FixedTables.D18.h171 else
  bif Nat.beq k 172 then Blueprint.CAP.FixedTables.D18.h172 else
  bif Nat.beq k 173 then Blueprint.CAP.FixedTables.D18.h173 else
  bif Nat.beq k 174 then Blueprint.CAP.FixedTables.D18.h174 else
  bif Nat.beq k 175 then Blueprint.CAP.FixedTables.D18.h175 else
  bif Nat.beq k 176 then Blueprint.CAP.FixedTables.D18.h176 else
  bif Nat.beq k 177 then Blueprint.CAP.FixedTables.D18.h177 else
  fun _ => []

theorem oldRows21 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG21 k ⟨m, h⟩ else []) 12 166 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
