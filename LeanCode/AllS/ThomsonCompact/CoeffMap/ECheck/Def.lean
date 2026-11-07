import ThomsonCompact.CoeffMap.EData
import ThomsonCompact.CoeffMap.RawD12
import ThomsonCompact.CoeffMap.SymEntries
import AllS.Units.N_AI.N_fixed_tables.D12.Data

/-!
# One-time table check: definitions (no `Interface` import)

`checkE bi` compares the packed sparse list `D12E.eList bi r` with `symEntries` of the proven raw tensors, for
all 100 retained coordinates `r` of block `bi`. One leaf module per block (`ECheck.B00` … `ECheck.B13`).
-/

namespace ThomsonCompact.CoeffMap.D12

open Blueprint.CAP Blueprint.Thomson Blueprint.Thomson.Finite

/-- Tag of retained coordinate `r`. -/
def tagN (r : Nat) : Tag := if h : r < 100 then FixedTables.D12.coordinateTags ⟨r, h⟩ else (0, 0, 0)

/-- Integer raw coefficient numerator of block `b` (with `blockCoef b t u v = blockZ b t u v / blockDen b`). -/
def blockZ : (b : GramBlock 6) → Tag → Fin (rawDim b) → Fin (rawDim b) → Int
  | .inl k => fun t u v => rawIntegerLookup (momSource k u v) t
  | .inr b => fun t u v => rawIntegerLookup (rawSource b u v) t

def blockDen : GramBlock 6 → Nat
  | .inl k => momDen k
  | .inr b => rawDen b

theorem blockCoef_eq (b : GramBlock 6) (t : Tag) (u v : Fin (rawDim b)) :
    blockCoef b t u v = (blockZ b t u v : ℚ) / (blockDen b : ℚ) := by
  cases b <;> rfl

/-- `blockZ` on `ℕ` indices (zero outside the block). -/
def zG (b : GramBlock 6) (t : Tag) (u v : Nat) : Int :=
  if h : u < rawDim b ∧ v < rawDim b then blockZ b t ⟨u, h.1⟩ ⟨v, h.2⟩ else 0

/-- Bool checker for block `bi`. -/
noncomputable def checkE (bi : Fin 14) : Bool :=
  Nat.beq (D12E.eSize bi) (rawDim (blockEquiv bi)) && Nat.beq (D12E.eDen bi) (blockDen (blockEquiv bi)) &&
    (List.range 100).all fun r => D12E.eList bi r == symEntries (zG (blockEquiv bi) (tagN r)) (D12E.eSize bi)

end ThomsonCompact.CoeffMap.D12
