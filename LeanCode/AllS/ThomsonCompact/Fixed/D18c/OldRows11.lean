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
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle046
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle047
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle048
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle049
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle050
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle051
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle052
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle053
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle054
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle055
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle056
import AllS.Units.N_AI.N_fixed_tables.D18.HSingle057

/-! Old `FixedTables.D18` rows 46–57 (`h046`–`h057`) against the compact slices (exact coefficient lists; F4c
identification leaf; imports only the old `HSingle` rows). -/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace ThomsonCompact.Fixed.D18c

open ThomsonCompact.Fixed

/-- The old rows 46–57. -/
noncomputable def oldG11 (k : Nat) : Fin 272 → List Int :=
  bif Nat.beq k 46 then Blueprint.CAP.FixedTables.D18.h046 else
  bif Nat.beq k 47 then Blueprint.CAP.FixedTables.D18.h047 else
  bif Nat.beq k 48 then Blueprint.CAP.FixedTables.D18.h048 else
  bif Nat.beq k 49 then Blueprint.CAP.FixedTables.D18.h049 else
  bif Nat.beq k 50 then Blueprint.CAP.FixedTables.D18.h050 else
  bif Nat.beq k 51 then Blueprint.CAP.FixedTables.D18.h051 else
  bif Nat.beq k 52 then Blueprint.CAP.FixedTables.D18.h052 else
  bif Nat.beq k 53 then Blueprint.CAP.FixedTables.D18.h053 else
  bif Nat.beq k 54 then Blueprint.CAP.FixedTables.D18.h054 else
  bif Nat.beq k 55 then Blueprint.CAP.FixedTables.D18.h055 else
  bif Nat.beq k 56 then Blueprint.CAP.FixedTables.D18.h056 else
  bif Nat.beq k 57 then Blueprint.CAP.FixedTables.D18.h057 else
  fun _ => []

theorem oldRows11 : rowsOldOk [slice0, slice1, slice2, slice3, slice4, slice5, slice6, slice7, slice8, slice9, slice10, slice11, slice12, slice13, slice14, slice15, slice16, slice17, slice18, slice19]
    (fun k m => if h : m < 272 then oldG11 k ⟨m, h⟩ else []) 12 46 = true := by
  decide +kernel

end ThomsonCompact.Fixed.D18c
