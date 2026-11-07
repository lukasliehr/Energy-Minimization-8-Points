import ThomsonCompact.CoeffMap.KRows
import ThomsonCompact.CoeffMap.Prog
import ThomsonCompact.CoeffMap.EData
import ThomsonCompact.CoeffMap.EDataG

/-!
# The D12 W0 block-contribution program (Init only; F2b)

Block `bi` (`blockEquiv` order: `F0 … F5`, then `M0_plus … Mdet_standard`), retained coordinate `r`, height TM
`A`, Gram TMs `WT i j` of the block: `blockTM c A WT bi r = gTMp c WT (blockRow c A bi) (eSize bi) (eList bi r) (eDen bi)` (`gTM` through the
materialized table of `pTM u v`).
A leaf checks `blockOk c A WT bi = true` (all 100 coordinates) by `decide +kernel`.
-/

namespace ThomsonCompact.CoeffMap

open ThomsonCompact.Packed

/-- Moment pivots of the D12 layout. -/
def pivN (k : Nat) : Nat := [0, 3, 2, 1, 0, 0].getD k 0

/-- Column counts of the scalar blocks (`scalarOrder`). -/
def sDimN (j : Nat) : Nat := [18, 5, 20, 22, 13, 6, 0, 4].getD j 0

/-- Rows of block `bi`. -/
noncomputable def blockRow (c : Ctx) (A : TM) (bi : Nat) : Nat → List (Nat × Option TM) :=
  if bi < 6 then momentRow c A bi (pivN bi) (6 - bi) else scalarRow c A (bi - 6) (sDimN (bi - 6))

/-- The W0 contribution TM of block `bi` to retained coordinate `r`. -/
noncomputable def blockTM (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (bi r : Nat) : TM :=
  gTMp c WT (blockRow c A bi) (D12E.eSize bi) (D12E.eList bi r) (D12E.eDen bi)

/-- Leaf checker: all 100 contributions of block `bi` are valid. -/
noncomputable def blockOk (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (bi : Nat) : Bool :=
  (List.range 100).all fun r => (blockTM c A WT bi r).ok

end ThomsonCompact.CoeffMap

namespace ThomsonCompact.CoeffMap

open ThomsonCompact.Packed

/-- Gram block dimension of block `bi`. -/
def gDimN (bi : Nat) : Nat := if bi < 6 then 6 - bi else sDimN (bi - 6)

/-- Rows of block `bi` with the faster records (`blockRowz_eq`). -/
noncomputable def blockRowz (c : Ctx) (A : TM) (bi : Nat) : Nat → List (Nat × Option TM) :=
  if bi < 6 then momentRow c A bi (pivN bi) (6 - bi) else scalarRowz c A (bi - 6) (sDimN (bi - 6))

/-- The W0 contribution TM of block `bi` to coordinate `r` (tabled contraction). -/
noncomputable def blockTMz (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (bi r : Nat) : TM :=
  gTMz c WT (blockRowz c A bi) (gDimN bi) (D12E.eSize bi) (D12E.eList bi r) (D12E.eDen bi)

/-- Leaf checker for the coordinates `r0 ≤ r < r1` of block `bi`. -/
noncomputable def blockOkz (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (bi r0 r1 : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun r ih => cond (Nat.ble r0 r) ((blockTMz c A WT bi r).ok && ih) ih) r1

/-- Group of a coefficient pair `(u, v)` under the group map `gmap` (5-bit slots over the raw rows: group in bits
0–3, bit 4 marks a pivot row). A pair follows `v`, except a pair of a dense `u` with a pivot row `v`, which
follows `u` (its products belong to row `u`); capped at `G - 1`. Any map is sound; it only balances leaves. -/
def grpOf (gmap G : Nat) (e : Nat × Nat × Bool × Nat) : Nat :=
  Nat.min ((fun su sv => cond (Nat.ble 16 sv && Nat.blt su 16) su (Nat.land sv 15))
    (slotAt 5 gmap e.1) (slotAt 5 gmap e.2.1)) (Nat.sub G 1)

/-- `k` entries peeled from the 32-bit slots of `x`. -/
noncomputable def peelE (k : Nat) : Nat → List (Nat × Nat × Bool × Nat) :=
  Nat.rec (motive := fun _ => Nat → List (Nat × Nat × Bool × Nat)) (fun _ => [])
    (fun _ ih x => D12E.decodeEntry (Nat.land x 4294967295) :: ih (Nat.shiftRight x 32)) k

/-- The entry stream of block `b` (every chunk numeral fetched once, its slots peeled sequentially). -/
noncomputable def eFlat (b : Nat) : List (Nat × Nat × Bool × Nat) :=
  (mkList (fun c => peelE 512 (D12E.entChunk b c)) (Nat.add (Nat.shiftRight (slotAt 16 (D12E.offs b) 100) 9) 1)).flatten

/-- Split a list into successive pieces of the given lengths. -/
noncomputable def splitC {α : Type} : List Nat → List α → List (List α) :=
  List.rec (motive := fun _ => List α → List (List α)) (fun _ => []) (fun k _ ih L => L.take k :: ih (L.drop k))

/-- All 100 coefficient lists of block `b` from one sequential decode (`= D12E.eList b r`, checked once in
`CoeffMap.ETabCheck`). -/
noncomputable def eTab (b : Nat) : List (List (Nat × Nat × Bool × Nat)) :=
  splitC (mkList (fun r => Nat.sub (slotAt 16 (D12E.offs b) (Nat.add r 1)) (slotAt 16 (D12E.offs b) r)) 100) (eFlat b)

/-- One-time check of the table of block `b`, coordinates `r0 ≤ r < r1`. -/
noncomputable def eTabOk (b r0 r1 : Nat) : Bool :=
  (List.range r1).all fun r => !(Nat.ble r0 r) || listAt [] (eTab b) r == D12E.eList b r

/-- The entry stream of pseudo-block `pb = 8 b + g` of the grouped tables. -/
noncomputable def eFlatG (pb : Nat) : List (Nat × Nat × Bool × Nat) :=
  (mkList (fun c => peelE 512 (D12G.entChunkG pb c))
    (Nat.add (Nat.shiftRight (slotAt 16 (D12G.offsG pb) 100) 9) 1)).flatten

/-- The 100 coefficient lists of pseudo-block `pb` (piece `g` of block `b`, `pb = 8 b + g`). -/
noncomputable def eTabG (pb : Nat) : List (List (Nat × Nat × Bool × Nat)) :=
  splitC (mkList (fun r => Nat.sub (slotAt 16 (D12G.offsG pb) (Nat.add r 1)) (slotAt 16 (D12G.offsG pb) r)) 100)
    (eFlatG pb)

/-- One-time check: the grouped lists of block `b`, groups `g0 ≤ g < g1`, are the filtered tables. -/
noncomputable def eGOk (b g0 g1 : Nat) : Bool :=
  (List.range g1).all fun g => !(Nat.ble g0 g) || (List.range 100).all fun r =>
    listAt [] (eTabG (Nat.add (Nat.mul 8 b) g)) r ==
      (listAt [] (eTab b) r).filter fun e => Nat.beq (grpOf (D12G.gmap b) 8 e) g

/-- Piece `g < 8` of block `bi` at coordinate `r`: the coefficient pairs of group `g` (grouped tables, tabled
contraction, faster records). -/
noncomputable def blockTMg (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (bi g r : Nat) : TM :=
  gTMz c WT (blockRowz c A bi) (gDimN bi) (D12E.eSize bi) (listAt [] (eTabG (Nat.add (Nat.mul 8 bi) g)) r)
    (D12E.eDen bi)

/-- Leaf checker: pieces `g0 ≤ g < g1` of block `bi`, all 100 coordinates. -/
noncomputable def blockOkg (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (bi g0 g1 : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun g ih => cond (Nat.ble g0 g)
    (Nat.rec (motive := fun _ => Bool) true (fun r ih2 => (blockTMg c A WT bi g r).ok && ih2) 100 && ih) ih) g1

end ThomsonCompact.CoeffMap
