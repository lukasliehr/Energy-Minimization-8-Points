import ThomsonCompact.Floor.B.Kernel

/-!
# F3d kernel (Init only): block leaves split by columns

For the large corrected blocks of D14/D16/D18 (orders up to 65) one `blockOk` leaf costs `O(n³)`; the leaves are split by
the column `q` of the pair loop: `blockOkQ` computes the pairs `p ≤ q` with `q ∈ [q0, q0+nq)` (zero metric entries and
untouched indices skipped, `stage1z`/`stage2z`) and bounds its packed row sums slotwise by stored partial sums;
`blockAggOk` sums the partial row sums of the column parts and does the Young checks. Mirror: `tools/reference/f3b.py`
(`block_split`).
-/

noncomputable section

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot)

/-! ## Block leaves split by columns (large blocks): partial row sums and one aggregation leaf -/

/-- `stage1` skipping zero metric entries (`Zi` is lower triangular) -/
def stage1z (wz zq : Nat) (tl : List (List (Nat × PAcc))) : List PAcc :=
  tl.map fun t => t.foldl (fun acc x => let z := zsm wz zq x.1; cond (Nat.beq z.2 0) acc (acc.addm z.1 z.2 x.2))
    PAcc.zero

/-- `stage2` skipping zero metric entries and untouched indices (`Y.A = 0`) -/
def stage2z (wz zp : Nat) (Ys : List PAcc) : PAcc :=
  (Ys.zip (List.range Ys.length)).foldl (fun acc x => let z := zsm wz zp x.2;
    cond (or (Nat.beq z.2 0) (Nat.beq x.1.A 0)) acc (acc.addm z.1 z.2 x.1)) PAcc.zero

/-- the double fold of `blockOk` over the columns `nzq ⊆ nz` (all pairs `p ≤ q`, `q ∈ nzq`) -/
def bfoldQ (c : Ctx) (wz FG LB LE LS ch0 nch smax : Nat) (okV : Bool) (ws : Nat → List Nat) (wE : List Nat)
    (nz nzq : List (Nat × Nat)) (tl : List (List (Nat × PAcc))) : List Nat × Nat × Bool × Nat :=
  nzq.foldl (fun (st : List Nat × Nat × Bool × Nat) zq =>
      let Ys := stage1z wz zq.1 tl
      nz.foldl (fun (st' : List Nat × Nat × Bool × Nat) zp =>
        cond (Nat.ble zp.2 zq.2)
          (let G := stage2z wz zp.1 Ys
           let Ts := (List.range nch).map fun ch =>
             zfin c FG (slot LB G.P ch, slot LB G.Q ch, Nat.mul G.A smax, slot LE G.E ch, okV)
           ((st'.1.zip (Ts.zip (List.range nch))).map fun x => rsAdd LS zp.2 zq.2 (range x.2.1) (ws (Nat.add ch0 x.2.2)) x.1,
            rsAdd LS zp.2 zq.2 (Packed.cdiv 64 G.H) wE st'.2.1,
            and st'.2.2.1 (Ts.all fun T => T.ok), Nat.max st'.2.2.2 G.A))
          st') st) (List.replicate nch 0, 0, true, 0)

/-- slotwise `rs ≤ R` on `n` slots of width `LS` -/
def slotsLe (LS n rs R : Nat) : Bool := (List.range n).all fun p => Nat.ble (slot LS rs p) (slot LS R p)

/-- **Block leaf, column part** `q ∈ [q0, q0+nq)`: the computation of `blockOk` restricted to these columns (pairs
`p ≤ q`), with the packed row sums bounded slotwise by the stored partial sums `Rp ch` (control channels `ch0 …
ch0+nch-1`) and `RpE` (error part) instead of the Young checks (done by `blockAggOk`). -/
def blockOkQ (cb : CellB) (row : Nat → RowT) (Kc wv we : Nat) (ckd : Nat → CkRow) (j0 nr n wz : Nat)
    (zrows : List Nat) (FG LB LE LS ch0 nch : Nat) (ws : Nat → List Nat) (wE : List Nat) (q0 nq : Nat)
    (Rp : Nat → Nat) (RpE : Nat) : Bool :=
  let c := cb.cT
  let js := (List.range nr).map (Nat.add j0)
  let pk := js.map fun j => ckPack c Kc wv we LB LE (ckd j) ch0 nch
  let uvV := (js.zip pk).map fun x => (((row x.1).u, (row x.1).v), x.2.1)
  let tl := (List.range n).map (touchV uvV)
  let okV := pk.all fun x => x.2.1
  let emax := pk.foldl (fun m x => Nat.max m x.2.2.1) 0
  let smax := pk.foldl (fun m x => Nat.max m x.2.2.2) 0
  let Ejmax := js.foldl (fun m j => Nat.max m (ckd j).Ej) 0
  let nz := zrows.zip (List.range n)
  let res := bfoldQ c wz FG LB LE LS ch0 nch smax okV ws wE nz ((nz.drop q0).take nq) tl
  let tzmax := res.2.2.2
  let Tmax := Nat.max (Nat.add (Nat.add c.twoB (Packed.cdiv FG (Nat.pow 2 LE))) c.m)
    (Packed.cdiv 64 (Nat.mul tzmax Ejmax))
  let wmax := (List.range nch).foldl (fun m i => (ws (Nat.add ch0 i)).foldl Nat.max m) (wE.foldl Nat.max 0)
  and (and (and (and res.2.2.1 (Nat.blt FG c.W)) (Nat.ble (Nat.add ch0 nch) (Nat.succ cb.N))) (and (Nat.beq zrows.length n)
      (and (Nat.blt (Nat.mul tzmax c.twoK) (Nat.pow 2 LB))
        (and (Nat.blt (Nat.mul tzmax emax) (Nat.pow 2 LE))
          (Nat.blt (Nat.mul (Nat.mul (Nat.mul n Tmax) wmax) 2) (Nat.pow 2 LS))))))
    (and ((res.1.zip (List.range nch)).all fun x => slotsLe LS n x.1 (Rp (Nat.add ch0 x.2)))
      (slotsLe LS n res.2.1 RpE))

/-- Young check of summed partial row sums: `w_p > 0`, `Σ_k slot_p(R_k) ≤ Γ w_p` -/
def youngSum (LS n : Nat) (Rs : List Nat) (w : List Nat) (Γ : Nat) : Bool :=
  (List.range n).all fun p =>
    and (Nat.blt 0 (w.getD p 0)) (Nat.ble (lsum (Rs.map fun R => slot LS R p)) (Nat.mul Γ (w.getD p 0)))

/-- **Block aggregation leaf** of the column parts `k` of a channel group (column counts `nqs_k`, consecutive from
`0`, summing to `n`; partial sums `Rps_k`, `RpEs_k`): Young checks of the summed row sums with the weights `ws ch`,
bounds `Γs ch`, `Γ 2^ex ≤ Gc Dc` (`ex = FG - κC - 64`), and the error part (`wE`, `Geta`). -/
def blockAggOk (cb : CellB) (n FG : Nat) (κC : Int) (Sc Gc LS ch0 nch : Nat) (nqs : List Nat)
    (Rps : List (Nat → Nat)) (RpEs : List Nat) (ws : Nat → List Nat) (Γs : Nat → Nat) (wE : List Nat) (Geta : Nat) :
    Bool :=
  let Dc := Nat.shiftLeft cb.D Sc
  let ex : Int := (FG : Int) - κC - 64
  and (and (Nat.beq (lsum nqs) n) (and (Nat.beq Rps.length nqs.length) (Nat.beq RpEs.length nqs.length)))
    (and ((List.range nch).all fun i =>
        and (youngSum LS n (Rps.map fun R => R (Nat.add ch0 i)) (ws (Nat.add ch0 i)) (Γs (Nat.add ch0 i)))
          (leShift (Γs (Nat.add ch0 i)) (Nat.mul Gc Dc) ex))
      (youngSum LS n RpEs wE Geta))

end ThomsonCompact.Floor.B

end
