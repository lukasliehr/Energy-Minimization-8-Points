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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle142
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle143
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle144
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle145
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle146
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle147
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle148
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle149
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle150
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle151
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle152
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle153

/-! Old `FixedTables.D18` rows 142–153 (`h142`–`h153`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 142–153. -/
noncomputable def oldG19 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 142 then Blueprint.CAP.FixedTables.D18.h142 else
  bif Nat.beq k 143 then Blueprint.CAP.FixedTables.D18.h143 else
  bif Nat.beq k 144 then Blueprint.CAP.FixedTables.D18.h144 else
  bif Nat.beq k 145 then Blueprint.CAP.FixedTables.D18.h145 else
  bif Nat.beq k 146 then Blueprint.CAP.FixedTables.D18.h146 else
  bif Nat.beq k 147 then Blueprint.CAP.FixedTables.D18.h147 else
  bif Nat.beq k 148 then Blueprint.CAP.FixedTables.D18.h148 else
  bif Nat.beq k 149 then Blueprint.CAP.FixedTables.D18.h149 else
  bif Nat.beq k 150 then Blueprint.CAP.FixedTables.D18.h150 else
  bif Nat.beq k 151 then Blueprint.CAP.FixedTables.D18.h151 else
  bif Nat.beq k 152 then Blueprint.CAP.FixedTables.D18.h152 else
  bif Nat.beq k 153 then Blueprint.CAP.FixedTables.D18.h153 else
  fun _ => []

theorem oldRows19 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG19 k ⟨m, h⟩ else []) 12 142 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
