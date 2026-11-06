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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle130
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle131
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle132
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle133
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle134
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle135
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle136
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle137
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle138
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle139
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle140
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle141

/-! Old `FixedTables.D18` rows 130–141 (`h130`–`h141`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 130–141. -/
noncomputable def oldG18 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 130 then Blueprint.CAP.FixedTables.D18.h130 else
  bif Nat.beq k 131 then Blueprint.CAP.FixedTables.D18.h131 else
  bif Nat.beq k 132 then Blueprint.CAP.FixedTables.D18.h132 else
  bif Nat.beq k 133 then Blueprint.CAP.FixedTables.D18.h133 else
  bif Nat.beq k 134 then Blueprint.CAP.FixedTables.D18.h134 else
  bif Nat.beq k 135 then Blueprint.CAP.FixedTables.D18.h135 else
  bif Nat.beq k 136 then Blueprint.CAP.FixedTables.D18.h136 else
  bif Nat.beq k 137 then Blueprint.CAP.FixedTables.D18.h137 else
  bif Nat.beq k 138 then Blueprint.CAP.FixedTables.D18.h138 else
  bif Nat.beq k 139 then Blueprint.CAP.FixedTables.D18.h139 else
  bif Nat.beq k 140 then Blueprint.CAP.FixedTables.D18.h140 else
  bif Nat.beq k 141 then Blueprint.CAP.FixedTables.D18.h141 else
  fun _ => []

theorem oldRows18 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG18 k ⟨m, h⟩ else []) 12 130 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
