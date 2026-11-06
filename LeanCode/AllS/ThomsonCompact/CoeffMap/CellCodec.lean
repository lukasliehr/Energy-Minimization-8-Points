import ThomsonCompact.CoeffMap.RFCodec
import ThomsonCompact.CoeffMap.MomentProg
import ThomsonCompact.Packed.Core2

/-!
# Per-cell W0 literal data: decoding and exact integer Gram coefficients (Init only; F2b d)

Layout (`tools/reference/FORMAT.md` §2): per block `bi` (`blockEquiv` order) `kdiag` (9-bit slots, offset
+128), `klow` (row-major strict lower triangle, signed slots `2|x| + [x<0]` of the per-cell width `kw`; 66 bits in
FORMAT.md §2 before F2d), `fac u` (row-major lower triangles, signed slots of width `w_b`), chunked in hex `Nat`s.

`coefI d bi k i j` is the exact integer coefficient of `tᵏ` in the literal Gram entry `(i, j)` at scale `2^-L`
(`L = max(2fb + NW, 2mb - e)`, `mb = max(mbits, -min dᵢ)`), as in `cellcheck.gram_coefficients`; the W0 entry
TM is `ofBoxes` of the exact rationals `coefI/2^L` (exact when `L ≤ S`). Soundness: `CoeffMap.GramSound`.
-/

namespace ThomsonCompact.CoeffMap

open ThomsonCompact.Packed

/-- Per-cell literal data (generated data module). -/
structure CellData where
  order : Nat → Nat
  kdiag : Nat → Nat
  klow : Nat → Nat → Nat
  fac : Nat → Nat → Nat → Nat
  layout : Nat → Nat × Nat × Nat
  nw : Nat
  fb : Nat
  mbits : Nat
  floorExp : Int
  /-- slot width of the `klow` fields (data-driven: max bit length of `2|x| + [x<0]`, at least 66) -/
  kw : Nat

/-- Signed slot `2|x| + [x<0]`. -/
def sdec (z : Nat) : Int :=
  if Nat.land z 1 = 1 then -(Int.ofNat (Nat.shiftRight z 1)) else Int.ofNat (Nat.shiftRight z 1)

/-- `count` slots from index `i` of a chunked field (`per` slots of width `w` per chunk). -/
def fieldRun (chunk : Nat → Nat) (w per : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | count + 1, i => slotAt w (chunk (i / per)) (i % per) :: fieldRun chunk w per count (i + 1)

def CellData.kdiagL (d : CellData) (bi : Nat) : List Int :=
  (List.range (d.order bi)).map fun i => Int.subNatNat (slotAt 9 (d.kdiag bi) i) 128

def CellData.klowL (d : CellData) (bi : Nat) : List Int :=
  (fieldRun (d.klow bi) d.kw (d.layout bi).1 (d.order bi * (d.order bi - 1) / 2) 0).map sdec

def CellData.facL (d : CellData) (bi u : Nat) : List Int :=
  (fieldRun (d.fac bi u) (d.layout bi).2.1 (d.layout bi).2.2 (d.order bi * (d.order bi + 1) / 2) 0).map sdec

/-- Dot product over the common prefix. -/
def dotI : List Int → List Int → Int
  | x :: xs, y :: ys => x * y + dotI xs ys
  | _, _ => 0

/-- Row `r` of a row-major lower triangle (entries `r(r+1)/2 … r(r+1)/2 + r`). -/
def lowerRow (flat : List Int) (r : Nat) : List Int := (flat.drop (r * (r + 1) / 2)).take (r + 1)

/-- `max(mbits, -min dᵢ)`. -/
def CellData.mb (d : CellData) (bi : Nat) : Nat :=
  (d.kdiagL bi).foldr (fun x m => Nat.max m (Int.toNat (-x))) d.mbits

/-- Row `r` of the metric scaled by `2^mb`: strict part `· 2^(mb - mbits)`, diagonal `2^(mb + dᵣ)`. -/
def CellData.metricRow (d : CellData) (bi r : Nat) : List Int :=
  (List.range (r + 1)).map fun l =>
    if l < r then (d.klowL bi).getD (r * (r - 1) / 2 + l) 0 * 2 ^ (d.mb bi - d.mbits)
    else 2 ^ (Int.toNat ((d.mb bi : Int) + (d.kdiagL bi).getD r 0))

/-- Monomial coefficient `k` of the Bernstein weight `u` times `2^NW`. -/
def bernI (nw u k : Nat) : Int :=
  (chooseI nw u : Int) * ((List.range (Nat.min u k + 1)).map fun j =>
    (if (k - j) % 2 = 0 then (1 : Int) else -1) * (chooseI u j : Int) * (chooseI (nw - u) (k - j) : Int)).foldr
      (· + ·) 0

/-- Gram scale `L = max(2 fb + NW, 2 mb - e)`. -/
def CellData.scaleL (d : CellData) (bi : Nat) : Nat :=
  Nat.max (2 * d.fb + d.nw) (Int.toNat (2 * (d.mb bi : Int) - d.floorExp))

/-- Exact integer coefficient of `tᵏ` in literal Gram entry `(i, j)` of block `bi`, scale `2^-L`. -/
def CellData.coefI (d : CellData) (bi k i j : Nat) : Int :=
  (if k = 0 then 2 ^ (d.scaleL bi - Int.toNat (2 * (d.mb bi : Int) - d.floorExp)) *
      dotI (d.metricRow bi i) (d.metricRow bi j) else 0) +
    ((List.range (d.nw + 1)).map fun u =>
      bernI d.nw u k * 2 ^ (d.scaleL bi - 2 * d.fb - d.nw) *
        dotI (lowerRow (d.facL bi u) i) (lowerRow (d.facL bi u) j)).foldr (· + ·) 0

/-- W0 entry TM `(i, j)` of block `bi` (boxes of the exact coefficients, zero error). -/
def CellData.w0TM (d : CellData) (c : Ctx) (bi i j : Nat) : TM :=
  ofBoxes c ((List.range (d.nw + 1)).map fun k =>
    (mkRat (d.coefI bi k i j) (2 ^ d.scaleL bi), mkRat (d.coefI bi k i j) (2 ^ d.scaleL bi))) 0

/-- W0 TMs of block `bi` on `ℕ` indices (zero outside the block; symmetric by construction). -/
def CellData.WT (d : CellData) (c : Ctx) (bi : Nat) (i j : Nat) : TM :=
  if i < d.order bi ∧ j < d.order bi then d.w0TM c bi (Nat.min i j) (Nat.max i j) else zeroTM

end ThomsonCompact.CoeffMap
