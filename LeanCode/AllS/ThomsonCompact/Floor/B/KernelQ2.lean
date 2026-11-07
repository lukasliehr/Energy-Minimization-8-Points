import ThomsonCompact.Floor.B.KernelQ

/-!
# F3f kernel (Init only): sequential column-split block leaves

`blockOkS` computes exactly what `blockOkQ` computes (`SoundBlockS.blockOkS_imp`), with sequential data access and
explicit recursion in the hot loops (profiles `Floor/B/Bench/ProfQ18*.lean`: the one-column D18 leaf 11.1 s → 4.9 s
from the data access alone):

* the rows' output coordinates `uvs` and checkpoints `cks` of the block as lists (instead of `row j`, `ckd j`:
  272-case `match` lookups, ~11 ms each);
* touch lists `touchR`, stage 1 `st1L`, stage 2 `st2L` (stops at `u > p`: `Zi` is lower triangular, checked by
  `zLower`) by explicit `List.rec`;
* the pairs `p ≤ q` of a column only (`colS`); weights as packed numerals (`ww`-bit slots, `rsAddN`).
-/

noncomputable section

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot)

/-- the block rows' output coordinates `(u, v)` from a packed numeral (two `w`-bit slots per row) -/
def uvList (w uvN nr : Nat) : List (Nat × Nat) :=
  (List.range nr).map fun i => (slot w uvN (Nat.mul 2 i), slot w uvN (Nat.add (Nat.mul 2 i) 1))

/-- the rows touching `u` (explicit recursion; `= touchV l u`) -/
def touchR {α : Type} (u : Nat) : List ((Nat × Nat) × α) → List (Nat × α) :=
  List.rec (motive := fun _ => List (Nat × α)) []
    (fun x _ ih => cond (Nat.beq x.1.1 u) ((x.1.2, x.2) :: ih)
      (cond (and (Nat.beq x.1.2 u) (Bool.not (Nat.beq x.1.1 u))) ((x.1.1, x.2) :: ih) ih))

/-- stage 1 of one touch list (explicit recursion) -/
def st1L (wz zq : Nat) : List (Nat × PAcc) → PAcc → PAcc :=
  List.rec (motive := fun _ => PAcc → PAcc) (fun acc => acc)
    (fun x _ ih acc => ih (cond (Nat.beq (zsm wz zq x.1).2 0) acc (acc.addm (zsm wz zq x.1).1 (zsm wz zq x.1).2 x.2)))

/-- stage 2 over the indices `u ≤ p` (explicit recursion, from index `u`) -/
def st2L (wz zp p : Nat) : List PAcc → Nat → PAcc → PAcc :=
  List.rec (motive := fun _ => Nat → PAcc → PAcc) (fun _ acc => acc)
    (fun Y _ ih u acc => cond (Nat.blt p u) acc
      (ih (Nat.succ u) (cond (or (Nat.beq (zsm wz zp u).2 0) (Nat.beq Y.A 0)) acc
        (acc.addm (zsm wz zp u).1 (zsm wz zp u).2 Y))))

/-- packed row sums with packed weights (`ww`-bit slots of `wN`) -/
def rsAddN (LS ww p q t wN acc : Nat) : Nat :=
  Nat.add (Nat.add acc (Nat.shiftLeft (Nat.mul t (slot ww wN q)) (Nat.mul LS p)))
    (cond (Nat.beq p q) 0 (Nat.shiftLeft (Nat.mul t (slot ww wN p)) (Nat.mul LS q)))

/-- the update of one pair `p ≤ q` (`wNs`: packed weights of the channels of the group) -/
def bupdS (c : Ctx) (FG LB LE LS ww nch smax : Nat) (okV : Bool) (wNs : List Nat) (wEN : Nat) (p q : Nat)
    (G : PAcc) (st : List Nat × Nat × Bool × Nat) : List Nat × Nat × Bool × Nat :=
  let Ts := (List.range nch).map fun ch =>
    zfin c FG (slot LB G.P ch, slot LB G.Q ch, Nat.mul G.A smax, slot LE G.E ch, okV)
  ((st.1.zip (Ts.zip wNs)).map fun x => rsAddN LS ww p q (range x.2.1) x.2.2 x.1,
   rsAddN LS ww p q (Packed.cdiv 64 G.H) wEN st.2.1,
   and st.2.2.1 (Ts.all fun T => T.ok), Nat.max st.2.2.2 G.A)

/-- the pairs `p ≤ q` of column `q` (the rows of `Zi` from index `p`) -/
def colS (c : Ctx) (wz FG LB LE LS ww nch smax : Nat) (okV : Bool) (wNs : List Nat) (wEN q : Nat) (Ys : List PAcc) :
    List Nat → Nat → List Nat × Nat × Bool × Nat → List Nat × Nat × Bool × Nat :=
  List.rec (motive := fun _ => Nat → List Nat × Nat × Bool × Nat → List Nat × Nat × Bool × Nat) (fun _ st => st)
    (fun zp _ ih p st => cond (Nat.blt q p) st
      (ih (Nat.succ p) (bupdS c FG LB LE LS ww nch smax okV wNs wEN p q (st2L wz zp p Ys 0 PAcc.zero) st)))

/-- the column fold over `cols` -/
def bfoldS (c : Ctx) (wz FG LB LE LS ww nch smax : Nat) (okV : Bool) (wNs : List Nat) (wEN : Nat)
    (zrows : List Nat) (cols : List (Nat × Nat)) (tl : List (List (Nat × PAcc))) : List Nat × Nat × Bool × Nat :=
  cols.foldl (fun st zq => colS c wz FG LB LE LS ww nch smax okV wNs wEN zq.2
    (tl.map fun t => st1L wz zq.1 t PAcc.zero) zrows 0 st) (List.replicate nch 0, 0, true, 0)

/-- `Zi` lower triangular: the slots of row `p` above `p` vanish -/
def zLower (wz : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun z _ ih p => and (Nat.beq (Nat.shiftRight z (Nat.mul wz (Nat.succ p))) 0) (ih (Nat.succ p)))

/-- **Block leaf, column part `q ∈ [q0, q0+nq)`, sequential**: `blockOkQ` with the rows `uvs`, checkpoints `cks`,
weights `wsN ch`/`wEN` (packed, `ww`-bit slots) -/
def blockOkS (cb : CellB) (uvs : List (Nat × Nat)) (cks : List CkRow) (Kc wv we n wz : Nat) (zrows : List Nat)
    (FG LB LE LS ch0 nch ww : Nat) (wsN : Nat → Nat) (wEN : Nat) (q0 nq : Nat) (Rp : Nat → Nat) (RpE : Nat) : Bool :=
  let c := cb.cT
  let pk := cks.map fun ck => ckPack c Kc wv we LB LE ck ch0 nch
  let uvV := (uvs.zip pk).map fun x => (x.1, x.2.1)
  let tl := (List.range n).map fun u => touchR u uvV
  let okV := pk.all fun x => x.2.1
  let emax := pk.foldl (fun m x => Nat.max m x.2.2.1) 0
  let smax := pk.foldl (fun m x => Nat.max m x.2.2.2) 0
  let Ejmax := cks.foldl (fun m ck => Nat.max m ck.Ej) 0
  let wNs := (List.range nch).map fun i => wsN (Nat.add ch0 i)
  let nz := zrows.zip (List.range n)
  let res := bfoldS c wz FG LB LE LS ww nch smax okV wNs wEN zrows ((nz.drop q0).take nq) tl
  let tzmax := res.2.2.2
  let Tmax := Nat.max (Nat.add (Nat.add c.twoB (Packed.cdiv FG (Nat.pow 2 LE))) c.m)
    (Packed.cdiv 64 (Nat.mul tzmax Ejmax))
  and (and (and (and res.2.2.1 (Nat.blt FG c.W)) (Nat.ble (Nat.add ch0 nch) (Nat.succ cb.N)))
      (and (and (Nat.beq zrows.length n) (zLower wz zrows 0))
        (and (Nat.blt (Nat.mul tzmax c.twoK) (Nat.pow 2 LB))
          (and (Nat.blt (Nat.mul tzmax emax) (Nat.pow 2 LE))
            (Nat.blt (Nat.mul (Nat.mul (Nat.mul n Tmax) (Nat.pow 2 ww)) 2) (Nat.pow 2 LS))))))
    (and ((res.1.zip (List.range nch)).all fun x => slotsLe LS n x.1 (Rp (Nat.add ch0 x.2)))
      (slotsLe LS n res.2.1 RpE))

/-- the rows' output coordinates of a block (`row` lookups; the leaves use `uvList` numerals checked against it) -/
def uvsOf (row : Nat → RowT) (j0 nr : Nat) : List (Nat × Nat) :=
  (List.range nr).map fun i => ((row (Nat.add j0 i)).u, (row (Nat.add j0 i)).v)

/-- the checkpoints of a block -/
def cksOf (ckd : Nat → CkRow) (j0 nr : Nat) : List CkRow := (List.range nr).map fun i => ckd (Nat.add j0 i)

/-- the error-part weights as a list (`n` slots of width `ww`) -/
def wEL (n ww wEN : Nat) : List Nat := (List.range n).map (slot ww wEN)

/-- the weights of channel `ch` as a list (`n` slots of width `ww`) -/
def wsL (n ww : Nat) (wsN : Nat → Nat) (ch : Nat) : List Nat := (List.range n).map (slot ww (wsN ch))

end ThomsonCompact.Floor.B

end
