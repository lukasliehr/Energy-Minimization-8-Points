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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle070
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle071
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle072
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle073
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle074
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle075
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle076
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle077
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle078
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle079
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle080
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle081

/-! Old `FixedTables.D18` rows 70–81 (`h070`–`h081`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 70–81. -/
noncomputable def oldG13 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 70 then Blueprint.CAP.FixedTables.D18.h070 else
  bif Nat.beq k 71 then Blueprint.CAP.FixedTables.D18.h071 else
  bif Nat.beq k 72 then Blueprint.CAP.FixedTables.D18.h072 else
  bif Nat.beq k 73 then Blueprint.CAP.FixedTables.D18.h073 else
  bif Nat.beq k 74 then Blueprint.CAP.FixedTables.D18.h074 else
  bif Nat.beq k 75 then Blueprint.CAP.FixedTables.D18.h075 else
  bif Nat.beq k 76 then Blueprint.CAP.FixedTables.D18.h076 else
  bif Nat.beq k 77 then Blueprint.CAP.FixedTables.D18.h077 else
  bif Nat.beq k 78 then Blueprint.CAP.FixedTables.D18.h078 else
  bif Nat.beq k 79 then Blueprint.CAP.FixedTables.D18.h079 else
  bif Nat.beq k 80 then Blueprint.CAP.FixedTables.D18.h080 else
  bif Nat.beq k 81 then Blueprint.CAP.FixedTables.D18.h081 else
  fun _ => []

theorem oldRows13 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG13 k ⟨m, h⟩ else []) 12 70 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
