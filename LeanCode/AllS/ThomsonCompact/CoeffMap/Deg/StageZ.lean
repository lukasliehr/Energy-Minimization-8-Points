import ThomsonCompact.CoeffMap.Deg.Prog

/-!
# Stored z columns: stage-Z checks and the stage-P `P` lookup (Init only; F2g)

For the heavy blocks the z entries `Z i v = Σ_{(j,e) ∈ row v} e · W i j` of the dense rows `v` are stored per cell as
**exact copies** (`ZData`, generated `Cells/<cell>/W0Z.lean`): record `(i, v)` holds the `m = N+1` coefficients of
`refresh (zTMD i v)` as biased slots of width `zw b` (`c_k + 2^(zw-1)`) and the error in a slot of width `ew b` above
them. Records of block `b` are numbered `rank(v) · gdim b + i` (`rank` = 8-bit slot `v` of `rk b`), `2^(ps b)` per numeral.

* `decZV`, `decZE`: the TM value and error fields of a record. The value is spread from the narrow slots to the `W`-bit
  TM slots in `zLv` levels of one mask, one subtraction, one shift and one addition each (`spread`), then unbiased.
  The decoder needs no soundness proof: the stage-Z check compares its output with the computed TM.
* `zStageOk` (stage-Z leaf): for the dense rows `v0 ≤ v < v1` and `i0 ≤ i < i1`, `zTMD i v` is `ok` and its value and
  error fields are the decoded stored ones (`zOk1`). Then `zDec … i v = refresh (zTMD i v)` (`CoeffMap.Deg.StageZSound`).
* `PS` (stage-P `P` lookup, used by the piece leaves `leafOk`): entry `(u, v)` is `P v u` (= `P u v`, `W` symmetric),
  so the owner `v` of a pair with a dense row `v` reads only its own row: dense-dense `R(v) · z(·, u)` (one dot product
  with the stored column `u`), pivot-dense `z(i_u, v)`, dense-pivot `z(j_v, u)` (stored), pivot-pivot `W j_v i_u`.
  The entries are tabled at literal indices (`pTS`): the pair indices of the class lists are decoded terms, and rows
  (records) evaluated at decoded indices would not be shared by the kernel.
  Soundness: `CoeffMap.Deg.StageZSound.PS_sound`. Bit-exact mirror: `CoeffMap/Deg/gen/mirror.py`.
-/

namespace ThomsonCompact.CoeffMap.Deg

open ThomsonCompact.Packed ThomsonCompact.CoeffMap

/-- Per-cell stored z data. -/
structure ZData where
  /-- block ↦ coefficient slot width -/
  zw : Nat → Nat
  /-- block ↦ error slot width -/
  ew : Nat → Nat
  /-- block ↦ dense rank table (8-bit slot `v`: rank of the dense row `v`) -/
  rk : Nat → Nat
  /-- block ↦ `log₂` of the records per numeral -/
  ps : Nat → Nat
  /-- block ↦ numeral `c` of the records -/
  chunk : Nat → Nat → Nat

/-! ## Decoding a record -/

/-- One spread level: keep the masked lower halves, move the rest up by `sh`. -/
def spreadStep (Mk sh y : Nat) : Nat := (fun lo => Nat.add lo (Nat.shiftLeft (Nat.sub y lo) sh)) (Nat.land y Mk)

/-- Mask of level `j` (`2^(L-1-j)` blocks of `2^(j+1)` slots, offsets `W 2^(j+1) t`): the lower `2^j` narrow slots. -/
def spreadMask (z W L j : Nat) : Nat :=
  Nat.mul (Nat.sub (Nat.shiftLeft 1 (Nat.mul z (Nat.shiftLeft 1 j))) 1)
    (ones (Nat.mul W (Nat.shiftLeft 1 (Nat.add j 1))) (Nat.shiftLeft 1 (Nat.sub (Nat.sub L j) 1)))

/-- Spread `2^L` narrow `z`-bit slots to `W`-bit slots: levels `j = k-1, …, 0` (`k = L` for the whole spread). -/
def spread (z W L : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun j ih y => ih (spreadStep (spreadMask z W L j) (Nat.mul (Nat.sub W z) (Nat.shiftLeft 1 j)) y))

/-- Number of spread levels for `m` slots (`2^zLv m ≥ m` for `m ≤ 64`). -/
def zLv (m : Nat) : Nat := cond (Nat.ble m 32) 5 6

/-- Value field of a record `x` (`m` biased `z`-bit slots, error above). -/
def decZV (c : Ctx) (z x : Nat) : Nat :=
  Nat.land (Nat.add (spread z c.W (zLv c.m) (zLv c.m) (Nat.land x (Nat.sub (Nat.shiftLeft 1 (Nat.mul z c.m)) 1)))
    (Nat.sub c.twoK (Nat.mul (Nat.shiftLeft 1 (Nat.sub z 1)) (ones c.W c.m)))) c.maskK

/-- Error field of a record `x`. -/
def decZE (c : Ctx) (z ew x : Nat) : Nat :=
  Nat.land (Nat.shiftRight x (Nat.mul z c.m)) (Nat.sub (Nat.shiftLeft 1 ew) 1)

namespace DegD

variable (L : DegD)

/-- Raw record of the stored entry `(i, v)` of block `b`. -/
def zRec (c : Ctx) (zd : ZData) (b i v : Nat) : Nat :=
  (fun k rw => Nat.land (Nat.shiftRight (zd.chunk b (Nat.shiftRight k (zd.ps b)))
      (Nat.mul rw (Nat.land k (Nat.sub (Nat.shiftLeft 1 (zd.ps b)) 1)))) (Nat.sub (Nat.shiftLeft 1 rw) 1))
    (Nat.add (Nat.mul (slotAt 8 (zd.rk b) v) (L.gdim b)) i) (Nat.add (Nat.mul c.m (zd.zw b)) (zd.ew b))

/-- The stored z entry `(i, v)` of block `b` as a TM (exact magnitudes recomputed). -/
def zDec (c : Ctx) (zd : ZData) (b i v : Nat) : TM :=
  (fun x => refresh c ⟨decZV c (zd.zw b) x, 0, 0, decZE c (zd.zw b) (zd.ew b) x, true⟩) (L.zRec c zd b i v)

/-- `T` is `ok` and has the value and error fields of the stored entry `(i, v)`. -/
def zOk1 (c : Ctx) (zd : ZData) (b i v : Nat) (T : TM) : Bool :=
  (fun x => T.ok && Nat.beq T.v (decZV c (zd.zw b) x) && Nat.beq T.e (decZE c (zd.zw b) (zd.ew b) x))
    (L.zRec c zd b i v)

/-- **Stage-Z leaf**: the z entries `(i, v)` of the dense rows `v0 ≤ v < v1`, `i0 ≤ i < i1`, match the stored copies. -/
noncomputable def zStageOk (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (zd : ZData) (b v0 v1 i0 i1 : Nat) : Bool :=
  (List.range (L.rdim b)).all fun v => !(Nat.ble v0 v && Nat.blt v v1) ||
    Option.casesOn (motive := fun _ => Bool) (pivotOf (L.blockRow c A b v))
      ((List.range (L.gdim b)).all fun i => !(Nat.ble i0 i && Nat.blt i i1) ||
        L.zOk1 c zd b i v (zTMD c (L.blockRow c A b) (wRowsD WT (L.gdim b)) i v))
      (fun _ => true)

/-- Entry `P v u` of block `b` at the table position `(u, v)` (stored dense z columns, W0 entries): dense-dense
`R(v) · z(·, u)`, dense-pivot `z(j_v, u)`, pivot-dense `z(i_u, v)`, pivot-pivot `W j_v i_u`. -/
noncomputable def pSB (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (zd : ZData) (b : Nat) (u v : Nat) : TM :=
  Option.casesOn (motive := fun _ => TM) (pivotOf (L.blockRow c A b u))
    (Option.casesOn (motive := fun _ => TM) (pivotOf (L.blockRow c A b v))
      (dotOpt c (zipRow (L.blockRow c A b v) (mkList (fun i => L.zDec c zd b i u) (L.gdim b)) 0))
      (fun j => L.zDec c zd b j u))
    (fun i => Option.casesOn (motive := fun _ => TM) (pivotOf (L.blockRow c A b v))
      (L.zDec c zd b i v)
      (fun j => WT j i))

/-- The table of all `pSB u v` (outer index `v`), built at literal indices so that every row is evaluated once. -/
noncomputable def pTS (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (zd : ZData) (b : Nat) : List (List TM) :=
  mkList (fun v => mkList (fun u => L.pSB c A WT zd b u v) (L.rdim b)) (L.rdim b)

/-- **Stage-P `P` lookup** of block `b`: entry `(u, v)` is `P v u` (= `P u v`) from the table `pTS` (zero outside
`[0, rdim b)²`). -/
noncomputable def PS (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (zd : ZData) (b : Nat) (u v : Nat) : TM :=
  listAt zeroTM (listAt [] (L.pTS c A WT zd b) v) u

end DegD

end ThomsonCompact.CoeffMap.Deg
