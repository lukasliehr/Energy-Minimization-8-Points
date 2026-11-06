import ThomsonCompact.CoeffMap.KRowsR

/-!
# Checkpointed W0 sums per retained coordinate (Init only; F2d)

For the centre gate (F3) the 112 contribution pieces of a cell are summed per retained coordinate `r`. The pieces of one
coordinate live in different leaves, so every piece TM is checkpointed (rounded to the scale `2^-(S-F)`):

* record `(bi, g, r)` (data `SumData`, generated `Cells/<cell>/W0Sum.lean`): `N+1` sign-magnitude slots `d_k`
  (`2|d|+[d<0]`) and an error slot `e'`, slot widths per block (`lay bi`, 9-bit slots); `ckOk c F T rec`:
  `Σ_k |c_k - d_k 2^F| + T.e ≤ e' 2^F` for the decoded coefficients `c_k` of `T` (units `2^-S`). Then the checkpoint
  QModel (`d_k 2^(F-S)`, error `e' 2^(F-S)`) encloses whatever `T` encloses (`CoeffMap.BSumSound.ck_valid`).
* leaf `blockOkS c A WT sd n bi g0 g1 r0 r1`: `ok` and `ckOk` (target order `n ≤ c.N`; the pieces may be computed at a
  higher order, the tail goes into the checkpoint error) of the pieces `g0 ≤ g < g1`, `r0 ≤ r < r1` of block `bi`;
  the coefficient lists `eTabG (8 bi + g)` are walked once (`walkP`; indexed lookups `listAt` into `eTabG` cost
  `O(r²)` kernel steps per piece: 0.15 GB / 1.5 s for the 800 pieces of an 8-group leaf).
* sum leaf `sumOk sd n r0 r1`: the final record `D r` has the exact sums of the checkpoints of the 26 nonempty pieces
  at `r` (coefficients) and at least their error sum; the pieces of the empty groups `g ≥ ngD12 bi` are zero
  (`emptyGroupsOk`, one-time per degree).
-/

namespace ThomsonCompact.CoeffMap

open ThomsonCompact.Packed

/-- Per-cell checkpoint data of the W0 sums. Lookups are `cond` trees on the index (a large `match` costs the kernel
`O(size)` per call). -/
structure SumData where
  /-- checkpoint scale shift: values at `2^-(S-F)` -/
  F : Nat
  /-- block ↦ slot widths `w_0 … w_N, w_e` (9-bit slots) -/
  lay : Nat → Nat
  /-- block ↦ record width `Σ widths` -/
  rw : Nat → Nat
  /-- block ↦ records per numeral -/
  per : Nat → Nat
  /-- numeral `16 (8 bi + g) + c` of the records of piece `(bi, g)` (record `r` is record `r` of this table) -/
  chunk : Nat → Nat
  /-- final sums: widths, record width, records per numeral, numerals -/
  dLay : Nat
  dRw : Nat
  dPer : Nat
  dChunk : Nat → Nat

/-- Number of nonempty pair groups of the D12 blocks (`D12G.gmap`, `edata_groups.py` splits `6:2,8:3,9:8,10:3`);
groups `g ≥ ngD12 bi` have empty coefficient lists (`emptyGroupsOk`). -/
def ngD12 (bi : Nat) : Nat :=
  cond (Nat.beq bi 6) 2 (cond (Nat.beq bi 8) 3 (cond (Nat.beq bi 9) 8 (cond (Nat.beq bi 10) 3 1)))

/-- One-time (per degree) check: the coefficient lists of the groups `g ≥ ngD12 bi` are empty. -/
noncomputable def emptyGroupsOk : Bool :=
  (List.range 14).all fun bi => (List.range 8).all fun g =>
    Nat.blt g (ngD12 bi) || (eTabG (Nat.add (Nat.mul 8 bi) g)).all List.isEmpty

/-- `n` slots of the record `x` with the widths of `ws` (9-bit slots), from width index `i`. -/
def decRec (ws : Nat) : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | n + 1, i, x => Nat.land x (Nat.sub (Nat.shiftLeft 1 (slotAt 9 ws i)) 1) ::
      decRec ws n (Nat.add i 1) (Nat.shiftRight x (slotAt 9 ws i))

/-- Raw record `r` of a table of records of width `rw`, `per` records per numeral. -/
def recRaw (ch : Nat → Nat) (rw per r : Nat) : Nat :=
  Nat.land (Nat.shiftRight (ch (Nat.div r per)) (Nat.mul rw (Nat.mod r per))) (Nat.sub (Nat.shiftLeft 1 rw) 1)

/-- Checkpoint slots of piece `(bi, g)` at coordinate `r` (`n+1` coefficients, then the error). -/
def ckRec (sd : SumData) (n bi g r : Nat) : List Nat :=
  decRec (sd.lay bi) (Nat.add n 2) 0
    (recRaw (fun c => sd.chunk (Nat.add (Nat.mul 16 (Nat.add (Nat.mul 8 bi) g)) c)) (sd.rw bi) (sd.per bi) r)

/-- Final sum slots at coordinate `r`. -/
def dRec (sd : SumData) (n r : Nat) : List Nat :=
  decRec sd.dLay (Nat.add n 2) 0 (recRaw sd.dChunk sd.dRw sd.dPer r)

/-- `|x - y|` on `ℕ`. -/
def absDiff (x y : Nat) : Nat := Nat.add (Nat.sub x y) (Nat.sub y x)

/-- `|c - d·2^F|` for the biased slot `b = c + H` and the sign-magnitude slot `z` of `d`. -/
def devK (H F b z : Nat) : Nat :=
  cond (Nat.beq (Nat.land z 1) 1) (absDiff (Nat.add b (Nat.shiftLeft (Nat.shiftRight z 1) F)) H)
    (absDiff b (Nat.add H (Nat.shiftLeft (Nat.shiftRight z 1) F)))

/-- `Σ_j devK (slot (k + j) of X) z_j`. -/
def devSum (W H F X : Nat) : Nat → List Nat → Nat
  | _, [] => 0
  | k, z :: zs => Nat.add (devK H F (slotAt W X k) z) (devSum W H F X (Nat.add k 1) zs)

/-- The `n+1` coefficient slots of a record, padded with zeros to `m` slots. -/
def padRec (n m : Nat) (rec : List Nat) : List Nat := rec.take (Nat.add n 1) ++ List.replicate (Nat.sub m (Nat.add n 1)) 0

/-- The checkpoint `rec` of target order `n ≤ c.N` encloses what `T` encloses: `Σ_{k ≤ N} |c_k - d_k 2^F| + e ≤ e' 2^F`
(units `2^-S`, `d_k = 0` for `k > n`: the TM's tail above the target order goes into the error). -/
def ckOk (c : Ctx) (F n : Nat) (T : TM) (rec : List Nat) : Bool :=
  Nat.ble (Nat.add (devSum c.W c.hW F (Nat.land (Nat.add T.v c.hb) c.maskK) 0 (padRec n c.m rec)) T.e)
    (Nat.shiftLeft (rec.getD (Nat.add n 1) 0) F)

/-- Walk a list of per-coordinate data once, from coordinate `r`: `p r x` for `r0 ≤ r < r1`. -/
noncomputable def walkP {α : Type} (p : Nat → α → Bool) (r0 r1 : Nat) : List α → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun x _ ih r =>
    cond (Nat.blt r r1) (cond (Nat.ble r0 r) (p r x && ih (Nat.add r 1)) (ih (Nat.add r 1))) true)

/-- One piece at coordinate `r` from its coefficient list `E` (precise rows `blockRowr`): `ok` and the checkpoint
`ck r`. -/
noncomputable def pieceOkS (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (bi : Nat) (ck : Nat → List Nat) (F n : Nat)
    (r : Nat) (E : List (Nat × Nat × Bool × Nat)) : Bool :=
  (fun T => T.ok && ckOk c F n T (ck r)) (gTMz c WT (blockRowr c A bi) (gDimN bi) (D12E.eSize bi) E (D12E.eDen bi))

/-- Leaf checker: pieces `g0 ≤ g < g1` of block `bi` at coordinates `r0 ≤ r < r1` are `ok` and match their
checkpoints (the coefficient lists `eTabG (8 bi + g)` are walked once). -/
noncomputable def blockOkS (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (sd : SumData) (n bi g0 g1 r0 r1 : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun g ih => cond (Nat.ble g0 g)
    (walkP (pieceOkS c A WT bi (ckRec sd n bi g) sd.F n) r0 r1 (eTabG (Nat.add (Nat.mul 8 bi) g)) 0 && ih) ih) g1

/-- Add the sign-magnitude slots `zs` to the `(positive, negative)` accumulators. -/
def accSM : List Nat → List (Nat × Nat) → List (Nat × Nat)
  | z :: zs, p :: acc => cond (Nat.beq (Nat.land z 1) 1) (p.1, Nat.add p.2 (Nat.shiftRight z 1))
      (Nat.add p.1 (Nat.shiftRight z 1), p.2) :: accSM zs acc
  | _, acc => acc

/-- Accumulate the records `L` (`m` coefficient slots, then the error). -/
def accRecs (m : Nat) : List (List Nat) → List (Nat × Nat) × Nat → List (Nat × Nat) × Nat
  | [], a => a
  | rec :: L, a => accRecs m L (accSM (rec.take m) a.1, Nat.add a.2 (rec.getD m 0))

/-- `sdec z = p - q` for the sign-magnitude slot `z`. -/
def smEq (z : Nat) (p : Nat × Nat) : Bool :=
  cond (Nat.beq (Nat.land z 1) 1) (Nat.beq p.2 (Nat.add (Nat.shiftRight z 1) p.1))
    (Nat.beq p.1 (Nat.add (Nat.shiftRight z 1) p.2))

/-- The checkpoint records of the nonempty pieces at coordinate `r` (block-major). -/
def recsAt (sd : SumData) (n r : Nat) : List (List Nat) :=
  (List.range 14).flatMap fun bi => (List.range (ngD12 bi)).map fun g => ckRec sd n bi g r

/-- Elementwise check of the final record against the accumulators. -/
def smAll : List Nat → List (Nat × Nat) → Bool
  | z :: zs, p :: ps => smEq z p && smAll zs ps
  | [], [] => true
  | _, _ => false

/-- The final record `D r` holds the coefficient sums and at least the error sum of the checkpoints of the nonempty
pieces (the others are zero). -/
def sumOkR (sd : SumData) (n r : Nat) : Bool :=
  (fun a => smAll ((dRec sd n r).take (Nat.add n 1)) a.1 && Nat.ble a.2 ((dRec sd n r).getD (Nat.add n 1) 0))
    (accRecs (Nat.add n 1) (recsAt sd n r) (List.replicate (Nat.add n 1) (0, 0), 0))

/-- Sum leaf: coordinates `r0 ≤ r < r1`. -/
def sumOk (sd : SumData) (n r0 r1 : Nat) : Bool :=
  (List.range r1).all fun r => !(Nat.ble r0 r) || sumOkR sd n r

end ThomsonCompact.CoeffMap
