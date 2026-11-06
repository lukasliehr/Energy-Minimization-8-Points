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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle094
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle095
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle096
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle097
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle098
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle099
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle100
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle101
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle102
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle103
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle104
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle105

/-! Old `FixedTables.D18` rows 94–105 (`h094`–`h105`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 94–105. -/
noncomputable def oldG15 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 94 then Blueprint.CAP.FixedTables.D18.h094 else
  bif Nat.beq k 95 then Blueprint.CAP.FixedTables.D18.h095 else
  bif Nat.beq k 96 then Blueprint.CAP.FixedTables.D18.h096 else
  bif Nat.beq k 97 then Blueprint.CAP.FixedTables.D18.h097 else
  bif Nat.beq k 98 then Blueprint.CAP.FixedTables.D18.h098 else
  bif Nat.beq k 99 then Blueprint.CAP.FixedTables.D18.h099 else
  bif Nat.beq k 100 then Blueprint.CAP.FixedTables.D18.h100 else
  bif Nat.beq k 101 then Blueprint.CAP.FixedTables.D18.h101 else
  bif Nat.beq k 102 then Blueprint.CAP.FixedTables.D18.h102 else
  bif Nat.beq k 103 then Blueprint.CAP.FixedTables.D18.h103 else
  bif Nat.beq k 104 then Blueprint.CAP.FixedTables.D18.h104 else
  bif Nat.beq k 105 then Blueprint.CAP.FixedTables.D18.h105 else
  fun _ => []

theorem oldRows15 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG15 k ⟨m, h⟩ else []) 12 94 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
