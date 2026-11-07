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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle154
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle155
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle156
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle157
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle158
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle159
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle160
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle161
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle162
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle163
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle164
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle165

/-! Old `FixedTables.D18` rows 154–165 (`h154`–`h165`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 154–165. -/
noncomputable def oldG20 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 154 then Blueprint.CAP.FixedTables.D18.h154 else
  bif Nat.beq k 155 then Blueprint.CAP.FixedTables.D18.h155 else
  bif Nat.beq k 156 then Blueprint.CAP.FixedTables.D18.h156 else
  bif Nat.beq k 157 then Blueprint.CAP.FixedTables.D18.h157 else
  bif Nat.beq k 158 then Blueprint.CAP.FixedTables.D18.h158 else
  bif Nat.beq k 159 then Blueprint.CAP.FixedTables.D18.h159 else
  bif Nat.beq k 160 then Blueprint.CAP.FixedTables.D18.h160 else
  bif Nat.beq k 161 then Blueprint.CAP.FixedTables.D18.h161 else
  bif Nat.beq k 162 then Blueprint.CAP.FixedTables.D18.h162 else
  bif Nat.beq k 163 then Blueprint.CAP.FixedTables.D18.h163 else
  bif Nat.beq k 164 then Blueprint.CAP.FixedTables.D18.h164 else
  bif Nat.beq k 165 then Blueprint.CAP.FixedTables.D18.h165 else
  fun _ => []

theorem oldRows20 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG20 k ⟨m, h⟩ else []) 12 154 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
