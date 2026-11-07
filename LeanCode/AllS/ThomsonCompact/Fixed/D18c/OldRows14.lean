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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle082
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle083
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle084
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle085
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle086
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle087
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle088
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle089
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle090
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle091
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle092
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle093

/-! Old `FixedTables.D18` rows 82–93 (`h082`–`h093`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 82–93. -/
noncomputable def oldG14 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 82 then Blueprint.CAP.FixedTables.D18.h082 else
  bif Nat.beq k 83 then Blueprint.CAP.FixedTables.D18.h083 else
  bif Nat.beq k 84 then Blueprint.CAP.FixedTables.D18.h084 else
  bif Nat.beq k 85 then Blueprint.CAP.FixedTables.D18.h085 else
  bif Nat.beq k 86 then Blueprint.CAP.FixedTables.D18.h086 else
  bif Nat.beq k 87 then Blueprint.CAP.FixedTables.D18.h087 else
  bif Nat.beq k 88 then Blueprint.CAP.FixedTables.D18.h088 else
  bif Nat.beq k 89 then Blueprint.CAP.FixedTables.D18.h089 else
  bif Nat.beq k 90 then Blueprint.CAP.FixedTables.D18.h090 else
  bif Nat.beq k 91 then Blueprint.CAP.FixedTables.D18.h091 else
  bif Nat.beq k 92 then Blueprint.CAP.FixedTables.D18.h092 else
  bif Nat.beq k 93 then Blueprint.CAP.FixedTables.D18.h093 else
  fun _ => []

theorem oldRows14 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG14 k ⟨m, h⟩ else []) 12 82 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
