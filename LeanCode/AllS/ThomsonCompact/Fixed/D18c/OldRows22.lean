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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle178
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle179
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle180
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle181
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle182
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle183
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle184
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle185
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle186
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle187
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle188
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle189

/-! Old `FixedTables.D18` rows 178–189 (`h178`–`h189`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 178–189. -/
noncomputable def oldG22 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 178 then Blueprint.CAP.FixedTables.D18.h178 else
  bif Nat.beq k 179 then Blueprint.CAP.FixedTables.D18.h179 else
  bif Nat.beq k 180 then Blueprint.CAP.FixedTables.D18.h180 else
  bif Nat.beq k 181 then Blueprint.CAP.FixedTables.D18.h181 else
  bif Nat.beq k 182 then Blueprint.CAP.FixedTables.D18.h182 else
  bif Nat.beq k 183 then Blueprint.CAP.FixedTables.D18.h183 else
  bif Nat.beq k 184 then Blueprint.CAP.FixedTables.D18.h184 else
  bif Nat.beq k 185 then Blueprint.CAP.FixedTables.D18.h185 else
  bif Nat.beq k 186 then Blueprint.CAP.FixedTables.D18.h186 else
  bif Nat.beq k 187 then Blueprint.CAP.FixedTables.D18.h187 else
  bif Nat.beq k 188 then Blueprint.CAP.FixedTables.D18.h188 else
  bif Nat.beq k 189 then Blueprint.CAP.FixedTables.D18.h189 else
  fun _ => []

theorem oldRows22 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG22 k ⟨m, h⟩ else []) 12 178 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
