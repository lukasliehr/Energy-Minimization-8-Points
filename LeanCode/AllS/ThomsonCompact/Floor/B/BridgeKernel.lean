import ThomsonCompact.Floor.B.Kernel

/-!
# F3b bridge kernel (Init only): the re-expanded table against the old `FixedTables.D12` literals

For an old entry `h : List ℤ` (`h(a) = Σ h_l a^l`) and the anchor `a0 = p/2^q`, `σ = 2^-g` (`cg = q - g`):
`reexpP` packs the integers `J_k` of `2^(q (len-1)) h((p + 2^cg u)/2^q) = Σ_k J_k u^k` by the recursion
`J(h₀ :: rest) = h₀ 2^(q |rest|) + (p + 2^cg X) J(rest)` (two's complement mod `2^K`, slot width `W`);
`reexpM` is the same recursion on `|h|` at `X = 1` (a bound for every `|J_k|`).
`entryOk` checks `2 |J_k 2^F⁺ - ê_k 2^(q(len-1) + F⁻)| ≤ 2^(q(len-1) + F⁻)` for every `k < dE`, i.e.
`|c_k 2^F - ê_k| ≤ 1/2` for the exact re-expanded coefficients `c_k` (`ê_k = 0` for the dropped `L ≤ k < dE`).
`rowBridgeOk` walks the entries `m < n` (`n` = number of input coordinates of the degree).
-/

noncomputable section

namespace ThomsonCompact.Floor.B
open ThomsonCompact.Packed
open ThomsonCompact.Floor (mask slot)

/-- packed `J` and `2^(q len)` -/
def reexpP (p q cg W K : Nat) : List Int → Nat × Nat :=
  List.rec (0, 1) (fun h _ ih =>
    let hp := Nat.mul (Int.natAbs h) ih.2
    let t := Nat.add (Nat.mul p ih.1) (Nat.shiftLeft ih.1 (Nat.add W cg))
    (Nat.land (cond (decide (h < 0)) (Nat.add t (Nat.sub (Nat.pow 2 K) (Nat.land hp (mask K)))) (Nat.add t hp))
      (mask K), Nat.shiftLeft ih.2 q))

/-- `Σ_l |h_l| (p + 2^cg)^l 2^(q (len-1-l))` and `2^(q len)` -/
def reexpM (p q cg : Nat) : List Int → Nat × Nat :=
  List.rec (0, 1) (fun h _ ih =>
    (Nat.add (Nat.mul (Int.natAbs h) ih.2) (Nat.mul (Nat.add p (Nat.pow 2 cg)) ih.1), Nat.shiftLeft ih.2 q))

/-- `|a - b|` -/
def ndist (a b : Nat) : Nat := Nat.add (Nat.sub a b) (Nat.sub b a)

/-- one coefficient: `J = (nJ, mJ)`, `ê = slot - 2^(w-1)`; `2 |J 2^Fp - ê 2^E| ≤ 2^E` (`E = q(len-1) + Fn`) -/
def coefOk (Fp E w : Nat) (J : Bool × Nat) (sl : Nat) : Bool :=
  let h := Nat.pow 2 (Nat.sub w 1)
  let eN := Nat.blt sl h
  let eM := ndist sl h
  let a := Nat.shiftLeft J.2 Fp
  let b := Nat.shiftLeft eM E
  Nat.ble (Nat.mul 2 (cond (Bool.not (xor J.1 eN)) (ndist a b) (Nat.add a b))) (Nat.pow 2 E)

/-- offset slot `ê_k + 2^(w-1)` of the entry at position `idx` (`ê_k = 0` for the dropped coefficients `k ≥ L`) -/
def eslot (r : RowT) (k idx : Nat) : Nat :=
  cond (Nat.blt k r.L) (slot r.w (r.t.getD k 0) idx) (Nat.pow 2 (Nat.sub r.w 1))

/-- the offset slots `ê_k + 2^(w-1)` (`k < dE`) of the entry at position `idx`, as a list -/
def eslots (r : RowT) (idx : Nat) : List Nat :=
  List.append (List.map (fun tk => slot r.w tk idx) r.t) (List.replicate (Nat.sub r.dE r.L) (Nat.pow 2 (Nat.sub r.w 1)))

/-- `coefOk` of the slots `0, 1, …` of a biased packed vector `Jb` (slot width `W`) against the list `es` -/
def coefsOk (Fp E w W : Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun s _ ih Jb => and (coefOk Fp E w (pbGet W Jb 0) s) (ih (Nat.shiftRight Jb W)))

/-- an entry at position `idx` of the row: `len ≤ dE`, the decode bound, every coefficient `k < dE` (one walk over
the biased packed `J` and the entry's offset slots) -/
def entryOk (p q g W : Nat) (r : RowT) (idx : Nat) (h : List Int) : Bool :=
  let len := h.length
  let K := Nat.mul W r.dE
  let J := reexpP p q (Nat.sub q g) W K h
  let M := reexpM p q (Nat.sub q g) h
  let Fp := Int.toNat r.F
  let E := Nat.add (Nat.mul q (Nat.sub len 1)) (Int.toNat (-r.F))
  and (and (and (Nat.ble len r.dE) (Nat.blt 0 len)) (Nat.blt M.1 (Nat.pow 2 (Nat.sub W 1))))
    (coefsOk Fp E r.w W (eslots r idx) (Nat.land (Nat.add J.1 (pvBias W r.dE)) (mask K)))

/-- magnitude bound of the entry at `idx`: `2 Σ_k |ê_k| 2^(uDg (L-1-k)) + dE 2^(uDg (L-1)) ≤ 2 mag 2^(uDg (L-1))` -/
def magOk (uDg : Nat) (r : RowT) (idx : Nat) (mag : Nat) : Bool :=
  let n := Nat.sub r.L 1
  let h := Nat.pow 2 (Nat.sub r.w 1)
  let num := lsum ((List.range r.L).map fun k =>
    Nat.shiftLeft (ndist (slot r.w (r.t.getD k 0) idx) h) (Nat.mul uDg (Nat.sub n k)))
  Nat.ble (Nat.add (Nat.mul 2 num) (Nat.shiftLeft r.dE (Nat.mul uDg n))) (Nat.shiftLeft (Nat.mul 2 mag) (Nat.mul uDg n))

/-- entries `m = m0, m0+1, …` (`fuel` of them) against the sorted entry list `ms` (positions from `idx`) -/
def rowEntriesOk (p q g W uDg : Nat) (r : RowT) (hrow : Nat → List Int) : Nat → Nat → Nat → List Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → List Nat → List Nat → Bool) (fun _ _ ms _ => List.isEmpty ms)
    (fun _ ih m idx ms mags =>
      List.rec (motive := fun _ => Bool) (and ((hrow m).all fun x => decide (x = 0)) (ih (Nat.succ m) idx [] []))
        (fun m' rest _ =>
          cond (Nat.beq m m')
            (and (and (entryOk p q g W r idx (hrow m)) (magOk uDg r idx (mags.headD 0)))
              (ih (Nat.succ m) (Nat.succ idx) rest mags.tail))
            (and (and ((hrow m).all fun x => decide (x = 0)) (Nat.blt m m')) (ih (Nat.succ m) idx ms mags)))
        ms)

/-- **Bridge check of a row** (entries `m < n`): `ms` sorted, every stored entry against the table entry,
every other entry zero, magnitude bounds, `|t| = L ≥ 1`, `L ≤ dE`, `w ≥ 1`; `W` = slot width of the packed `J`. -/
def rowBridgeOk (n p q g W uDg : Nat) (r : RowT) (hrow : Nat → List Int) : Bool :=
  and (and (Nat.beq r.msL.length r.nms) (and (Nat.beq r.t.length r.L) (and (Nat.blt 0 r.L)
      (and (Nat.blt 0 r.w) (Nat.ble r.L r.dE)))))
    (rowEntriesOk p q g W uDg r hrow n 0 0 r.msL r.magL)

/-- **Denominator bridge** (`λ d = λ/dq · dz`, `dz` integers): `2 |J^d_k λ 2^Fd⁺ - d̂_k dq 2^E| ≤ dq 2^E` -/
def denOk (p q g W : Nat) (r : RowT) (lam : Nat) (dq : Nat) (dz : List Int) : Bool :=
  let len := dz.length
  let K := Nat.mul W r.Ld
  let J := reexpP p q (Nat.sub q g) W K dz
  let M := reexpM p q (Nat.sub q g) dz
  let Fp := Int.toNat r.Fd
  let E := Nat.add (Nat.mul q (Nat.sub len 1)) (Int.toNat (-r.Fd))
  and (and (and (Nat.ble len r.Ld) (Nat.blt 0 len)) (and (Nat.blt M.1 (Nat.pow 2 (Nat.sub W 1))) (Nat.blt 0 dq)))
    ((List.range r.Ld).all fun k =>
      let Jk := pvGet W r.Ld J.1 k
      let d := r.dhL.getD k (false, 0)
      let a := Nat.shiftLeft (Nat.mul Jk.2 lam) Fp
      let b := Nat.shiftLeft (Nat.mul d.2 dq) E
      Nat.ble (Nat.mul 2 (cond (Bool.not (xor Jk.1 d.1)) (ndist a b) (Nat.add a b))) (Nat.mul dq (Nat.pow 2 E)))

end ThomsonCompact.Floor.B

end
