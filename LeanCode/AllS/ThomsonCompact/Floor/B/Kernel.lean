import ThomsonCompact.Packed.Core2
import ThomsonCompact.Floor.Kernel

/-!
# F3b kernel (Init only): packed correction and floor bounds

Bit-exact with `tools/reference/f3b.py` (same names). The centre polynomials of the residual enter through their
Bernstein controls (convexity in the cell variable), the height through Taylor models in the height-box variable
`t ∈ [-1,1]` (`u = (a - a0)/σ = u_c + ρ_u t`), the right-inverse table through its re-expanded rounded form in `u`.

* packed integer vectors (channels): `v ≡ Σ zᵢ 2^(W i) mod 2^(W n)`; `pvGet` (signed slot), `pvAbs` (magnitudes);
* `contractK`: exact `Σ_m ê_m c_m` of offset slots `ê + 2^(w-1)` against channel vectors;
* `zcomb c F terms`: exact `Σ ±nᵢ Tᵢ` of packed TMs, one per-slot floor shift by `F` (F1 `round_signed` in the
  rounding context `mkCtx N F B W`), exact magnitudes (`pabs`);
* `rowOk`, `blockOk`, `errOk`, `heightOk`, `centreOk`: the leaf checks.
-/

noncomputable section

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot)

/-! ## Small helpers -/

/-- `Σ` of a list (explicit recursor) -/
def lsum : List Nat → Nat := List.rec 0 (fun x _ ih => Nat.add x ih)

/-- sign-magnitude slot `2|x| + [x<0]` as `(negative?, |x|)` -/
def smDec (z : Nat) : Bool × Nat := (Nat.beq (Nat.land z 1) 1, Nat.shiftRight z 1)

/-- `x · 2^a ≤ y · 2^b` for an integer exponent split `e = a - b` (`a = e⁺`, `b = e⁻`) -/
def leShift (x y : Nat) (e : Int) : Bool :=
  Nat.ble (Nat.shiftLeft x (Int.toNat e)) (Nat.shiftLeft y (Int.toNat (-e)))

/-! ## Packed integer vectors (channels) -/

def pvBias (W n : Nat) : Nat := Nat.mul (Nat.pow 2 (Nat.sub W 1)) (ones W n)

/-- signed slot `i` of `v ≡ Σ z 2^(W i) mod 2^(W n)`: `(z < 0, |z|)` (needs `|z| < 2^(W-1)`) -/
def pvGet (W n v i : Nat) : Bool × Nat :=
  let h := Nat.pow 2 (Nat.sub W 1)
  let d := slot W (Nat.land (Nat.add v (pvBias W n)) (mask (Nat.mul W n))) i
  (Nat.blt d h, Nat.add (Nat.sub d h) (Nat.sub h d))

/-- packed magnitudes of a biased vector `X = (v + bias) mod 2^(W n)` (F1 `pabs` after its first step) -/
def pbAbs (W n X : Nat) : Nat :=
  let hb := pvBias W n
  let mK := mask (Nat.mul W n)
  let h := Nat.land X hb
  let pm := Nat.mul (Nat.shiftRight h (Nat.sub W 1)) (mask W)
  Nat.add (Nat.sub (Nat.land X pm) h) (Nat.sub (Nat.sub hb h) (Nat.land X (Nat.sub mK pm)))

/-- packed magnitudes `Σ |zᵢ| 2^(W i)` (F1 `pabs` with the mask `2^(W n) - 1`) -/
def pvAbs (W n v : Nat) : Nat := pbAbs W n (Nat.land (Nat.add v (pvBias W n)) (mask (Nat.mul W n)))

/-! ## Contraction with the transposed table -/

/-- `acc + Σ_idx slot_idx(t) · cv_idx` (slots of width `w`, `mw = 2^w - 1`) -/
def dotOff (w mw : Nat) : List Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun cv _ ih t acc => ih (Nat.shiftRight t w) (Nat.add acc (Nat.mul (Nat.land t mw) cv)))

/-- `Σ_idx (slot_idx(t) - 2^(w-1)) cv_idx mod 2^KC` (`sumcv = Σ cv`) -/
def contractK (w KC : Nat) (cvs : List Nat) (sumcv t : Nat) : Nat :=
  Nat.land (Nat.add (dotOff w (mask w) cvs t 0)
    (Nat.sub (Nat.pow 2 KC) (Nat.land (Nat.mul (Nat.pow 2 (Nat.sub w 1)) sumcv) (mask KC)))) (mask KC)

/-! ## Exact combinations of packed Taylor models -/

/-- accumulators `(P, Q, Σ n s, Σ n e, ok)` of `Σ ±n T` (positive and negative parts apart) -/
def zacc : List (Bool × Nat × TM) → Nat → Nat → Nat → Nat → Bool → Nat × Nat × Nat × Nat × Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool → Nat × Nat × Nat × Nat × Bool)
    (fun P Q ns ne ok => (P, Q, ns, ne, ok))
    (fun x _ ih P Q ns ne ok =>
      ih (cond x.1 P (Nat.add P (Nat.mul x.2.1 x.2.2.v))) (cond x.1 (Nat.add Q (Nat.mul x.2.1 x.2.2.v)) Q)
        (Nat.add ns (Nat.mul x.2.1 x.2.2.s)) (Nat.add ne (Nat.mul x.2.1 x.2.2.e)) (and ok x.2.2.ok))

/-- the TM `2^-F (P - Q)` from accumulators: exact difference mod `2^K`, per-slot floor shift by `F` (rounding
context `mkCtx N F B W`), exact magnitudes, error `⌈ne / 2^F⌉ + (N+1)`, overflow check `ns < 2^(2B)` -/
def zfin (c : Ctx) (F : Nat) (r : Nat × Nat × Nat × Nat × Bool) : TM :=
  let cF := mkCtx c.N F c.B c.W
  let V := Nat.land (Nat.add r.1 (Nat.sub c.twoK (Nat.land r.2.1 c.maskK))) c.maskK
  let v := Nat.land (Nat.add (Nat.shiftRight (Nat.land (Nat.land (Nat.add V cF.biasP) cF.maskK) cF.rmask) F)
    cF.unb) cF.maskK
  let a := pabs c ⟨v, 0, 0, 0, true⟩
  let s := ssum c a
  ⟨v, a, s, Nat.add (Packed.cdiv F r.2.2.2.1) c.m,
   and (and r.2.2.2.2 (Nat.blt r.2.2.1 (Nat.pow 2 (Nat.mul 2 c.B)))) (Nat.blt s c.twoB)⟩

/-- `2^-F Σ ±nᵢ Tᵢ` -/
def zcomb (c : Ctx) (F : Nat) (terms : List (Bool × Nat × TM)) : TM := zfin c F (zacc terms 0 0 0 0 true)

/-- signed slot `i` of a *biased* packed vector `Pb = (v + bias) mod 2^(W n)` -/
def pbGet (W Pb i : Nat) : Bool × Nat :=
  let h := Nat.pow 2 (Nat.sub W 1)
  let d := slot W Pb i
  (Nat.blt d h, Nat.add (Nat.sub d h) (Nat.sub h d))

/-- `(P, Q)` of `Σ_k ±|P_k,ch| W_k.v` (biased contraction results `Pb`, TMs `Ws`) -/
def zaccB (W ch : Nat) : List Nat → List TM → Nat → Nat → Nat × Nat :=
  List.rec (motive := fun _ => List TM → Nat → Nat → Nat × Nat) (fun _ P Q => (P, Q))
    (fun Pb _ ih Ws P Q =>
      List.rec (motive := fun _ => Nat × Nat) (P, Q)
        (fun Wk Ws' _ =>
          let g := pbGet W Pb ch
          ih Ws' (cond g.1 P (Nat.add P (Nat.mul g.2 Wk.v))) (cond g.1 (Nat.add Q (Nat.mul g.2 Wk.v)) Q)) Ws)

/-- exact affine TM `±a0 + a1 t` (scale `2^-S`) -/
def tmAff (c : Ctx) (ng : Bool) (a0 a1 : Nat) : TM :=
  ofPQ c (Nat.add (cond ng 0 a0) (Nat.shiftLeft a1 c.W)) (cond ng a0 0) 0

/-- `[P, P·U, P·U², …]` (`n` entries) -/
def upowL (c : Ctx) (U : TM) : Nat → TM → List TM :=
  Nat.rec (motive := fun _ => TM → List TM) (fun _ => []) (fun _ ih P => P :: ih (mul c P U))

/-- `[1, U, …, U^n]` -/
def upow (c : Ctx) (U : TM) (n : Nat) : List TM := upowL c U (Nat.succ n) (constTM c false c.twoS 0)

/-- pair coefficients with TMs (shorter list wins) -/
def zipT : List (Bool × Nat) → List TM → List (Bool × Nat × TM) :=
  List.rec (motive := fun _ => List TM → List (Bool × Nat × TM)) (fun _ => [])
    (fun g _ ih Us => List.rec (motive := fun _ => List (Bool × Nat × TM)) [] (fun U Us' _ => (g.1, g.2, U) :: ih Us') Us)

/-! ## Per-degree table rows -/

/-- One re-expanded table row: entries `ms` (`nms` slots of width `wms`), `L` coefficients per entry with
transposed offset numerals `t` (slot `idx` of `t_k` = `ê_{ms[idx],k} + 2^(w-1)`), exponent `F`
(`|2^F H(a0+σu) - Σ_{k<L} ê u^k| ≤ dE/2` on `|u| ≤ 1`: `dE = L` for a full re-expansion, `dE > L` when trailing
coefficients rounding to zero are dropped), denominator `2^Fd λ d(a0+σu) ≈ Σ d̂ u^k` (`Ld` sign-magnitude slots of
width `wd`), magnitude bounds `mag` (`nms` slots of width `wm`: `|2^F H| ≤ mag` for `|u| ≤ u_D`), output coordinate
`(u, v)`. -/
structure RowT where
  ms : Nat
  nms : Nat
  L : Nat
  w : Nat
  F : Int
  t : List Nat
  Ld : Nat
  Fd : Int
  dh : Nat
  wd : Nat
  mag : Nat
  wm : Nat
  u : Nat
  v : Nat
  wms : Nat := 8
  dE : Nat := L

def RowT.msL (r : RowT) : List Nat := (List.range r.nms).map (slot r.wms r.ms)
def RowT.dhL (r : RowT) : List (Bool × Nat) := (List.range r.Ld).map fun k => smDec (slot r.wd r.dh k)
def RowT.magL (r : RowT) : List Nat := (List.range r.nms).map (slot r.wm r.mag)

/-- shift of the denominators -/
def FDP : Nat := 100

/-! ## Channel vectors: Bernstein controls of the centres and target directions -/

def chooseF (n k : Nat) : Nat := cond (Nat.ble k n) (Nat.div (fact n) (Nat.mul (fact k) (fact (Nat.sub n k)))) 0

/-- `D_N = lcm_k C(N,k)` -/
def bernDen (N : Nat) : Nat := (List.range (Nat.succ N)).foldl (fun D k => Nat.lcm D (chooseF N k)) 1

/-- `β̃_ik = (Σ_j (-1)^(k-j) C(i,j) C(N-i,k-j)) · D/C(N,k)` as `(negative?, |·|)` -/
def bernI (N D i k : Nat) : Bool × Nat :=
  let terms := List.range (Nat.succ k)
  let pos := lsum (terms.map fun j => cond (Nat.beq (Nat.mod (Nat.sub k j) 2) 0)
    (Nat.mul (chooseF i j) (chooseF (Nat.sub N i) (Nat.sub k j))) 0)
  let ng := lsum (terms.map fun j => cond (Nat.beq (Nat.mod (Nat.sub k j) 2) 1)
    (Nat.mul (chooseF i j) (chooseF (Nat.sub N i) (Nat.sub k j))) 0)
  let q := Nat.div D (chooseF N k)
  (Nat.blt pos ng, Nat.mul (Nat.add (Nat.sub pos ng) (Nat.sub ng pos)) q)

/-- column `k` of `β̃`, packed over the channels `i ≤ N` (two's complement mod `2^KC`) -/
def bcol (N D WC KC k : Nat) : Nat :=
  let ents := (List.range (Nat.succ N)).map fun i => bernI N D i k
  let P := packD WC (ents.map fun b => cond b.1 0 b.2)
  let Q := packD WC (ents.map fun b => cond b.1 b.2 0)
  Nat.land (Nat.add P (Nat.sub (Nat.pow 2 KC) Q)) (mask KC)

/-- `max_i |β̃_ik|` -/
def bmax (N D k : Nat) : Nat := (List.range (Nat.succ N)).foldl (fun m i => Nat.max m (bernI N D i k).2) 0

/-- control part of the channel vector of a coordinate: `Σ_k C_k bcol_k mod 2^M` (`M = WC (N+1)`), centre
coefficients `C_k` (sign-magnitude slots of width `wc` in `cm`) -/
def chanCtl (N M wc : Nat) (bcols : List Nat) (cm : Nat) : Nat :=
  let cs := (List.range (Nat.succ N)).map fun k => smDec (slot wc cm k)
  let acc := (cs.zip bcols).foldl (fun (pq : Nat × Nat) x =>
    cond x.1.1 (pq.1, Nat.add pq.2 (Nat.mul x.1.2 x.2)) (Nat.add pq.1 (Nat.mul x.1.2 x.2), pq.2)) (0, 0)
  Nat.land (Nat.add acc.1 (Nat.sub (Nat.pow 2 M) (Nat.land acc.2 (mask M)))) (mask M)

/-- bound check of the channel values of a coordinate: `Σ_k |C_k| bmax_k ≤ cmax`, `|qn| ≤ cmax` -/
def chanBnd (N wc cmax : Nat) (bmaxs : List Nat) (cm : Nat) (dq : Bool × Nat) : Bool :=
  let cs := (List.range (Nat.succ N)).map fun k => (smDec (slot wc cm k)).2
  and (Nat.ble (lsum ((cs.zip bmaxs).map fun x => Nat.mul x.1 x.2)) cmax) (Nat.ble dq.2 cmax)

/-! ## Per-cell inputs -/

/-- Per-cell parameters and data (`cm m`: centre numeral of coordinate `m`; `cvc`: control parts of the channel
vectors (verified against `cm` by `chanOk`); `dirT m`, `dirQ m`: target direction of coordinate `m`; `Er m`: box
radius (`2^-S`); `herr t`: target-model error (`2^-S`)). -/
structure CellB where
  N : Nat
  Kt : Nat
  BT : Nat
  WC : Nat
  wc : Nat
  cmax : Nat
  ucNeg : Bool
  ucN : Nat
  rN : Nat
  cm : Nat → Nat
  cvc : List Nat
  dirT : Nat → Nat
  dirQ : Nat → Bool × Nat
  Er : Nat → Nat
  herr : Nat → Nat
  nT : Nat

def CellB.nC (cb : CellB) : Nat := Nat.add (Nat.succ cb.N) cb.nT
def CellB.KC (cb : CellB) : Nat := Nat.mul cb.WC cb.nC
def CellB.M (cb : CellB) : Nat := Nat.mul cb.WC (Nat.succ cb.N)
def CellB.cT (cb : CellB) : Ctx := mkCtx cb.Kt 256 cb.BT (Nat.add (Nat.mul 2 cb.BT) 2)
def CellB.D (cb : CellB) : Nat := bernDen cb.N
def CellB.bcols (cb : CellB) : List Nat :=
  (List.range (Nat.succ cb.N)).map (bcol cb.N cb.D cb.WC cb.KC)
def CellB.bmaxs (cb : CellB) : List Nat := (List.range (Nat.succ cb.N)).map (bmax cb.N cb.D)
def CellB.U (cb : CellB) : TM := tmAff cb.cT cb.ucNeg cb.ucN cb.rN

/-- **Channel leaf**: the stored control parts are the Bernstein transforms of the centres, value bounds -/
def chanOk (cb : CellB) (nin : Nat) : Bool :=
  and (and (Nat.beq cb.cvc.length nin)
      ((cb.cvc.zip (List.range nin)).all fun x => Nat.beq x.1 (chanCtl cb.N cb.M cb.wc cb.bcols (cb.cm x.2))))
    (and ((List.range nin).all fun m => and (chanBnd cb.N cb.wc cb.cmax cb.bmaxs (cb.cm m) (cb.dirQ m))
      (Nat.blt (cb.dirT m) cb.nT))
    (and (Nat.blt (Nat.mul 2 cb.cmax) (Nat.pow 2 cb.WC))
      (and cb.U.ok (and (Nat.blt cb.ucN (Nat.pow 2 (Nat.add (Nat.mul 2 cb.BT) 2)))
        (and (Nat.blt cb.rN (Nat.pow 2 (Nat.add (Nat.mul 2 cb.BT) 2)))
          (and (Nat.ble (Nat.mul 2 (Nat.add cb.ucN cb.rN)) (Nat.pow 2 256)) (Nat.ble 1 cb.Kt)))))))

/-- all channel vectors: the control part (sign-extended from `M = WC (N+1)` to `KC` bits) plus the direction
`±qn 2^(WC (N+1+t))`, mod `2^KC` -/
def chanAll (KC M WC N1 : Nat) (dirT : Nat → Nat) (dirQ : Nat → Bool × Nat) : List Nat → Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun cv _ ih m =>
      let dq := dirQ m
      let d := Nat.shiftLeft dq.2 (Nat.mul WC (Nat.add N1 (dirT m)))
      let cx := cond (Nat.beq (Nat.land (Nat.shiftRight cv (Nat.sub M 1)) 1) 1)
        (Nat.add cv (Nat.sub (Nat.pow 2 KC) (Nat.pow 2 M))) cv
      Nat.land (cond dq.1 (Nat.add cx (Nat.sub (Nat.pow 2 KC) d)) (Nat.add cx d)) (mask KC) :: ih (Nat.succ m))

/-- the elements of `all` (indexed from `m`) at the sorted positions `ms` -/
def selectL : List Nat → List Nat → Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → Nat → List Nat) (fun _ _ => [])
    (fun x _ ih ms m =>
      List.rec (motive := fun _ => List Nat) [] (fun m' ms' _ => cond (Nat.beq m m') (x :: ih ms' (Nat.succ m)) (ih ms (Nat.succ m))) ms)

/-! ## Row leaf -/

/-- checkpoint TM from compact data: `Kc+1` sign-magnitude slots of width `wv` and the error `e`, all in units
`2^g` (of `2^-S`) -/
def ckTM (c : Ctx) (Kc g wv x e : Nat) : TM :=
  let sl := (List.range (Nat.succ Kc)).map fun k => smDec (slot wv x k)
  ofPQ c (packD c.W (sl.map fun z => cond z.1 0 (Nat.shiftLeft z.2 g)))
    (packD c.W (sl.map fun z => cond z.1 (Nat.shiftLeft z.2 g) 0)) (Nat.shiftLeft e g)

/-- checkpoint acceptance: `rangeX (V - Ṽ) + V.e ≤ Ṽ.e` -/
def ckOk (c : Ctx) (V Vt : TM) : Bool :=
  let Dd := add c (polyOnly V) (neg c (polyOnly Vt))
  and (and (and V.ok Vt.ok) Dd.ok) (Nat.ble (Nat.add (rangeX c Dd) V.e) Vt.e)

/-- checkpoint data of a row: per control channel `ch ≤ N` the coefficient slots
(`Kc+1` of width `wv`, block `ch`) and the error (slot of width `we` in `errs`); the error claim `Ej` -/
structure CkRow where
  g : Nat
  coef : Nat
  errs : Nat
  Ej : Nat

/-- checkpoint TM of control channel `ch` -/
def CkRow.tm (ck : CkRow) (c : Ctx) (Kc wv we ch : Nat) : TM :=
  ckTM c Kc ck.g wv (slot (Nat.mul wv (Nat.succ Kc)) ck.coef ch) (slot we ck.errs ch)

/-- the row computation: denominator `D`, reciprocal `R`, channel TMs `V` (`cvs`: channel vectors of the row):
`W_k = U^k · R`, `V_ch = 2^-F' Σ_k P_k,ch W_k` widened by the table rounding `δ_ch · rangeX R` (`dE/2` per entry);
`ns_ch = (Σ_k |P_k,ch|) max_k W_k.s`, `ne_ch = (Σ_k |P_k,ch|) max_k W_k.e` -/
def rowTMs (cb : CellB) (Us : List TM) (r : RowT) (cvs : List Nat) (FpC FpD : Nat) : TM × TM × List TM :=
  let c := cb.cT
  let KC := cb.KC
  let hb := pvBias cb.WC cb.nC
  let Pb := r.t.map fun t => Nat.land (Nat.add (contractK r.w KC cvs (lsum cvs) t) hb) (mask KC)
  let As := lsum (cvs.map (pvAbs cb.WC cb.nC))
  let Dt := widen (zcomb c FDP (zipT r.dhL Us)) (Packed.cdiv (Nat.succ FDP) (Nat.shiftLeft r.Ld 256))
  let Rr := invN c 8 0 Dt
  let rR := rangeX c Rr
  let Ws := (Us.take r.L).map fun U => mul c U Rr
  let PA := lsum (Pb.map (pbAbs cb.WC cb.nC))
  let Wsm := Ws.foldl (fun m W => Nat.max m W.s) 0
  let Wem := Ws.foldl (fun m W => Nat.max m W.e) 0
  let okW := Ws.all TM.ok
  let V := (List.range cb.nC).map fun ch =>
    let Fp := cond (Nat.ble ch cb.N) FpC FpD
    let pq := zaccB cb.WC ch Pb Ws 0 0
    widen (zfin c Fp (pq.1, pq.2, Nat.mul (slot cb.WC PA ch) Wsm, Nat.mul (slot cb.WC PA ch) Wem, okW))
      (Packed.cdiv 256 (Nat.mul (Packed.cdiv (Nat.succ Fp) (Nat.shiftLeft (Nat.mul r.dE (slot cb.WC As ch)) 256)) rR))
  (Dt, Rr, V)

/-- shifts `F' = F - Fd + FDP - κ` (must be `≥ 0`) -/
def fShift (r : RowT) (κ : Int) : Int := r.F - r.Fd + (FDP : Int) - κ

/-- **Row check**: overflow bounds, `D`, `R`, every channel TM `ok`, checkpoints of the control channels,
error claim `Ẽ_j` (`str = Σ_t herr_t rangeX(V_(N+1+t))`, `box = Σ_m mag_m Er_m · rangeX(R)`). -/
def rowOk (cb : CellB) (Us : List TM) (cvA : List Nat) (r : RowT) (κC κD : Int) (Kc wv we : Nat) (ck : CkRow) :
    Bool :=
  let FpC := fShift r κC
  let FpD := fShift r κD
  let res := rowTMs cb Us r (selectL cvA r.msL 0) (Int.toNat FpC) (Int.toNat FpD)
  let c := cb.cT
  let V := res.2.2
  let ctrl := (List.range (Nat.succ cb.N)).all fun ch => ckOk c (V.getD ch zeroTM) (ck.tm c Kc wv we ch)
  let strj := lsum ((List.range cb.nT).map fun t =>
    Nat.mul (cb.herr t) (rangeX c (V.getD (Nat.add (Nat.succ cb.N) t) zeroTM)))
  let mer := lsum ((r.msL.zip r.magL).map fun x => Nat.mul x.2 (cb.Er x.1))
  let rhs := Nat.add (Nat.shiftLeft strj (Int.toNat FpD)) (Nat.mul (Nat.mul 3 mer) (rangeX c res.2.1))
  let chk1 := and (decide (0 ≤ FpC ∧ 0 ≤ FpD)) (and (Nat.blt (Int.toNat FpC) c.W)
    (and (Nat.blt (Int.toNat FpD) c.W) (and (Nat.blt FDP c.W) (and (Nat.ble r.L Us.length) (Nat.ble r.Ld Us.length)))))
  let chk2 := Nat.blt (Nat.mul (Nat.mul (Nat.mul r.L r.nms) (Nat.pow 2 (Nat.sub r.w 1))) cb.cmax)
    (Nat.pow 2 (Nat.sub cb.WC 1))
  let chk3 := and res.1.ok (and res.2.1.ok (V.all fun T => T.ok))
  and (and chk1 (and chk2 chk3)) (and ctrl (leShift rhs (Nat.shiftLeft (Nat.mul 3 ck.Ej) (Int.toNat FpD)) (-(256 + κD))))

/-- **Row leaf**: rows `j0 … j0+n-1` of the table `row` (one block: `κC`, `κD`), checkpoints `ckd` -/
def rowsOk (cb : CellB) (row : Nat → RowT) (Lmax : Nat) (κC κD : Int) (Kc wv we : Nat) (ckd : Nat → CkRow)
    (j0 n : Nat) : Bool :=
  let Us := upow cb.cT cb.U Lmax
  let cvA := chanAll cb.KC cb.M cb.WC (Nat.succ cb.N) cb.dirT cb.dirQ cb.cvc 0
  (List.range n).all fun i => rowOk cb Us cvA (row (Nat.add j0 i)) κC κD Kc wv we (ckd (Nat.add j0 i))

/-! ## Block leaf: channel-packed two-stage congruence `Z M Zᵀ` and the error part -/

/-- `Zi_pu` as `(negative?, magnitude)` (row numeral `zr`, slot width `wz`) -/
def zsm (wz zr u : Nat) : Bool × Nat := smDec (slot wz zr u)

/-- the rows of a block touching index `u`, as `(other index, payload)` (`u_j = u`: other `v_j`;
`v_j = u ≠ u_j`: other `u_j`) -/
def touchV {α : Type} (uvV : List ((Nat × Nat) × α)) (u : Nat) : List (Nat × α) :=
  uvV.filterMap fun x => cond (Nat.beq x.1.1 u) (some (x.1.2, x.2))
    (cond (and (Nat.beq x.1.2 u) (Bool.not (Nat.beq x.1.1 u))) (some (x.1.1, x.2)) none)

/-- exact accumulator: channel-packed `P - Q` (values) and `E` (errors), scalars `H` (error part `Σ |c| Ẽ`) and
`A` (`Σ |c|`) -/
structure PAcc where
  P : Nat
  Q : Nat
  E : Nat
  H : Nat
  A : Nat

def PAcc.zero : PAcc := ⟨0, 0, 0, 0, 0⟩

/-- `acc + (±n) · x` -/
def PAcc.addm (acc : PAcc) (ng : Bool) (n : Nat) (x : PAcc) : PAcc :=
  ⟨Nat.add acc.P (Nat.mul n (cond ng x.Q x.P)), Nat.add acc.Q (Nat.mul n (cond ng x.P x.Q)),
   Nat.add acc.E (Nat.mul n x.E), Nat.add acc.H (Nat.mul n x.H), Nat.add acc.A (Nat.mul n x.A)⟩

/-- packed checkpoint TMs of a row (control channels `ch0 … ch0+nch-1`): `(⟨Σ v 2^(LB i), 0, Σ e 2^(LE i), Ẽ, 1⟩,
all ok, max e, max s)` -/
def ckPack (c : Ctx) (Kc wv we LB LE : Nat) (ck : CkRow) (ch0 nch : Nat) : PAcc × Bool × Nat × Nat :=
  let r := (List.range nch).foldr (fun i (a : Nat × Nat × Bool × Nat × Nat) =>
    let T := ck.tm c Kc wv we (Nat.add ch0 i)
    (Nat.add T.v (Nat.shiftLeft a.1 LB), Nat.add T.e (Nat.shiftLeft a.2.1 LE), and T.ok a.2.2.1,
      Nat.max T.e a.2.2.2.1, Nat.max T.s a.2.2.2.2)) (0, 0, true, 0, 0)
  (⟨r.1, 0, r.2.1, ck.Ej, 1⟩, r.2.2.1, r.2.2.2.1, r.2.2.2.2)

/-- stage 1 for fixed `q`: `Y_uq = Σ_{(o, X) ∈ touch u} Zi_qo X` for every `u` -/
def stage1 (wz zq : Nat) (tl : List (List (Nat × PAcc))) : List PAcc :=
  tl.map fun t => t.foldl (fun acc x => let z := zsm wz zq x.1; acc.addm z.1 z.2 x.2) PAcc.zero

/-- stage 2: `G_pq = Σ_u Zi_pu Y_uq` -/
def stage2 (wz zp : Nat) (Ys : List PAcc) : PAcc :=
  (Ys.zip (List.range Ys.length)).foldl (fun acc x => let z := zsm wz zp x.2; acc.addm z.1 z.2 x.1) PAcc.zero

/-- packed row sums: `acc + t (w_q 2^(LS p) + [p ≠ q] w_p 2^(LS q))` -/
def rsAdd (LS p q t : Nat) (w : List Nat) (acc : Nat) : Nat :=
  Nat.add (Nat.add acc (Nat.shiftLeft (Nat.mul t (w.getD q 0)) (Nat.mul LS p)))
    (cond (Nat.beq p q) 0 (Nat.shiftLeft (Nat.mul t (w.getD p 0)) (Nat.mul LS q)))

/-- Young check of packed row sums: `w_p > 0`, `(T w)_p ≤ Γ w_p` -/
def youngChk (LS n : Nat) (rs : Nat) (w : List Nat) (Γ : Nat) : Bool :=
  (List.range n).all fun p => and (Nat.blt 0 (w.getD p 0)) (Nat.ble (slot LS rs p) (Nat.mul Γ (w.getD p 0)))

/-- **Block leaf** (control channels `ch0 … ch0+nch-1` of the block rows `j0 … j0+nr-1`): channel-packed two-stage
exact `Σ_j Tz_pq,j Ṽ_j` per pair `p ≤ q`, per channel `G = zfin FG` and `T = range G`, Young with the weights
`ws ch` and bounds `Γs ch`, `Γ 2^ex ≤ Gc Dc` (`ex = FG - κC - 64`); error part
`T^η_pq = ⌈Σ_u |Zi_pu| Σ_{touch u} |Zi_qo| Ẽ / 2^64⌉`, Young with the weights `wE` and bound `Geta`;
strides `LB` (values), `LE` (errors), `LS` (row sums) with the no-overflow checks. -/
def blockOk (cb : CellB) (row : Nat → RowT) (Kc wv we : Nat) (ckd : Nat → CkRow) (j0 nr n wz : Nat)
    (zrows : List Nat) (FG : Nat) (κC : Int) (Sc Gc LB LE LS ch0 nch : Nat) (ws : Nat → List Nat) (Γs : Nat → Nat)
    (wE : List Nat) (Geta : Nat) : Bool :=
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
  let res := nz.foldl (fun (st : List Nat × Nat × Bool × Nat) zq =>
      let Ys := stage1 wz zq.1 tl
      nz.foldl (fun (st' : List Nat × Nat × Bool × Nat) zp =>
        cond (Nat.ble zp.2 zq.2)
          (let G := stage2 wz zp.1 Ys
           let Ts := (List.range nch).map fun ch =>
             zfin c FG (slot LB G.P ch, slot LB G.Q ch, Nat.mul G.A smax, slot LE G.E ch, okV)
           ((st'.1.zip (Ts.zip (List.range nch))).map fun x => rsAdd LS zp.2 zq.2 (range x.2.1) (ws (Nat.add ch0 x.2.2)) x.1,
            rsAdd LS zp.2 zq.2 (Packed.cdiv 64 G.H) wE st'.2.1,
            and st'.2.2.1 (Ts.all fun T => T.ok), Nat.max st'.2.2.2 G.A))
          st') st) (List.replicate nch 0, 0, true, 0)
  let tzmax := res.2.2.2
  let Tmax := Nat.max (Nat.add (Nat.add c.twoB (Packed.cdiv FG (Nat.pow 2 LE))) c.m)
    (Packed.cdiv 64 (Nat.mul tzmax Ejmax))
  let wmax := (List.range nch).foldl (fun m i => (ws (Nat.add ch0 i)).foldl Nat.max m) (wE.foldl Nat.max 0)
  let Dc := Nat.shiftLeft cb.D Sc
  let ex : Int := (FG : Int) - κC - 64
  and (and (and (and res.2.2.1 (Nat.blt FG c.W)) (Nat.ble (Nat.add ch0 nch) (Nat.succ cb.N))) (and (Nat.beq zrows.length n)
      (and (Nat.blt (Nat.mul tzmax c.twoK) (Nat.pow 2 LB))
        (and (Nat.blt (Nat.mul tzmax emax) (Nat.pow 2 LE))
          (Nat.blt (Nat.mul (Nat.mul (Nat.mul n Tmax) wmax) 2) (Nat.pow 2 LS))))))
    (and ((res.1.zip (List.range nch)).all fun x =>
      and (youngChk LS n x.1 (ws (Nat.add ch0 x.2)) (Γs (Nat.add ch0 x.2))) (leShift (Γs (Nat.add ch0 x.2)) (Nat.mul Gc Dc) ex))
      (youngChk LS n res.2.1 wE Geta))

/-! ## Height box and centre gate -/

/-- `|a(x) - ac 2^-S| ≤ rg 2^-S` on the cell from the height TM `A` -/
def heightOk (c : Ctx) (A : TM) (ac rg : Nat) : Bool :=
  and (addC c true ac 0 A).ok (Nat.ble (rangeX c (addC c true ac 0 A)) rg)

/-- exact `Σ ±n T` mod `2^K` and the decode bound `Σ n s < 2^(W-1)` (all `ok`) -/
def zval (c : Ctx) (terms : List (Bool × Nat × TM)) : Nat × Bool :=
  let r := zacc terms 0 0 0 0 true
  (Nat.land (Nat.add r.1 (Nat.sub c.twoK (Nat.land r.2.1 c.maskK))) c.maskK,
   and r.2.2.2.2 (Nat.blt r.2.2.1 c.hW))

/-- `|x - y|` of sign-magnitude numbers -/
def smDist (x y : Bool × Nat) : Nat :=
  cond (Bool.not (xor x.1 y.1)) (Nat.add (Nat.sub x.2 y.2) (Nat.sub y.2 x.2)) (Nat.add x.2 y.2)

/-- `(⌊z/3⌋, ⌈z/3⌉)` of a sign-magnitude `z` -/
def div3 (z : Bool × Nat) : (Bool × Nat) × (Bool × Nat) :=
  cond z.1 ((true, Nat.div (Nat.add z.2 2) 3), (true, Nat.div z.2 3))
    ((false, Nat.div z.2 3), (false, Nat.div (Nat.add z.2 2) 3))

/-- **Centre gate** of coordinate `i`: `v = qn H_t - 3 Σ_b B_b` (exact), `lo/hi = ⌊v/3⌋, ⌈v/3⌉`,
`Σ_k max(|lo_k - C_k 2^(S-Sc)|, |hi_k - C_k 2^(S-Sc)|) + Σ_b e_b ≤ Er`
(`cm`: centre slots of width `wc`) -/
def centreOk1 (c : Ctx) (Sc wc : Nat) (Ht : TM) (dq : Bool × Nat) (Bs : List TM) (cm Er : Nat) : Bool :=
  let z := zval c ((dq.1, dq.2, Ht) :: Bs.map fun B => (true, 3, B))
  let n2 := Nat.succ (Nat.mul 2 c.N)
  let tot := lsum ((List.range (Nat.succ c.N)).map fun k =>
    let lh := div3 (pvGet c.W n2 z.1 k)
    let cc := smDec (slot wc cm k)
    let C' := (cc.1, Nat.shiftLeft cc.2 (Nat.sub c.S Sc))
    Nat.max (smDist lh.1 C') (smDist lh.2 C'))
  and (and z.2 (Nat.ble Sc c.S)) (Nat.ble (Nat.add tot (lsum (Bs.map fun B => B.e))) Er)

/-- **Centre gate leaf**: coordinates `i < nin`; `H t` target TMs, `Bs i` contributions -/
def centreOk (c : Ctx) (Sc wc : Nat) (H : Nat → TM) (dirT : Nat → Nat) (dirQ : Nat → Bool × Nat)
    (Bs : Nat → List TM) (cm Er : Nat → Nat) (nin : Nat) : Bool :=
  (List.range nin).all fun i => centreOk1 c Sc wc (H (dirT i)) (dirQ i) (Bs i) (cm i) (Er i)

end ThomsonCompact.Floor.B

end
