/-!
# Fixed right-inverse tables: kernel programs (Init only; workstream F4)

Checked identity (for each degree): `Σ_k (N_ik Γ_k)(B) · H_ki'(B) = [i = i'] s Q(B)` at the radix `B = 2^R`.

Encodings (all `Nat`, chunks of ≤ 16 kbit, first 8 bits = number of records in the chunk):
* **polynomial record**: header `idx` (bits 0–11), `L` (12–19), `w` (20–27), then `L` biased slots
  `c + 2^(w-1)` of `w` bits, **highest coefficient first**; value at `2^R` by Horner (`polyVal`);
* **value record**: header `idx` (0–11), `nb` (12–31), then an `nb`-bit payload `2|v| + [v < 0]` (`valOf`).

A vector (row/column) is a chunk sequence with strictly increasing indices. Hot loops use explicit
recursors. Soundness: `Fixed.KernelSound`; bit-exact Python mirror: `tools/f4_export.py`.
-/

namespace ThomsonCompact.Fixed

/-! ## Fields and signed values -/

def mask (w : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 w) 1

/-- Bits `[off, off + w)` of `x`. -/
def fld (x off w : Nat) : Nat := Nat.land (Nat.shiftRight x off) (mask w)

/-- Sign-magnitude form of `p - q`. -/
noncomputable def sm (p q : Nat) : Bool × Nat :=
  Bool.rec (false, Nat.sub p q) (true, Nat.sub q p) (Nat.blt p q)

/-! ## Polynomial records -/

/-- Horner over `L` slots of width `w` (`mk = 2^w - 1`) of `x`, highest slot first: `acc·2^(RL) + Σ`. -/
noncomputable def hornerU (R w mk : Nat) (L : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun _ ih x acc => ih (Nat.shiftRight x w) (Nat.add (Nat.shiftLeft acc R) (Nat.land x mk))) L

/-- `Σ_{l<L} 2^(R l)`. -/
def onesR (R L : Nat) : Nat := Nat.div (mask (Nat.mul R L)) (mask R)

/-- Value at `2^R` of the polynomial record at the bottom of `x` (header `L = fld x 12 8`, `w = fld x 20 8`). -/
noncomputable def polyVal (R x : Nat) : Bool × Nat :=
  sm (hornerU R (Nat.land (Nat.shiftRight x 20) 255) (Nat.sub (Nat.shiftLeft 1 (Nat.land (Nat.shiftRight x 20) 255)) 1)
      (Nat.land (Nat.shiftRight x 12) 255) (Nat.shiftRight x 28) 0)
    (Nat.mul (Nat.shiftLeft 1 (Nat.sub (Nat.land (Nat.shiftRight x 20) 255) 1)) (onesR R (Nat.land (Nat.shiftRight x 12) 255)))

/-- Bit length of the polynomial record at the bottom of `x`. -/
def polyLen (x : Nat) : Nat :=
  Nat.add 28 (Nat.mul (Nat.land (Nat.shiftRight x 12) 255) (Nat.land (Nat.shiftRight x 20) 255))

/-- Decode `n` polynomial records: `(idx, sign, magnitude)` at `2^R`. -/
noncomputable def decPolys (R : Nat) (n : Nat) : Nat → List (Nat × Bool × Nat) :=
  Nat.rec (motive := fun _ => Nat → List (Nat × Bool × Nat)) (fun _ => [])
    (fun _ ih x => (Nat.land x 4095, polyVal R x) :: ih (Nat.shiftRight x (polyLen x))) n

/-- Header checks of `n` polynomial records: `1 ≤ w ≤ wmax`, `L ≤ Lmax`, indices `≥ lo`, strictly increasing,
`< hi`. Returns `1 +` the next admissible index, or `0` on failure. -/
noncomputable def polysOk (Lmax wmax hi : Nat) (n : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun lo _ => Nat.add lo 1)
    (fun _ ih lo x =>
      Bool.rec 0 (ih (Nat.add (Nat.land x 4095) 1) (Nat.shiftRight x (polyLen x)))
        (Nat.ble 1 (Nat.land (Nat.shiftRight x 20) 255) && Nat.ble (Nat.land (Nat.shiftRight x 20) 255) wmax &&
          Nat.ble (Nat.land (Nat.shiftRight x 12) 255) Lmax &&
          Nat.ble lo (Nat.land x 4095) && Nat.blt (Nat.land x 4095) hi)) n

/-! ## Value records: `idx` (bits 0–11), sign (bit 12), `nb` (13–31), magnitude (`nb` bits) -/

/-- Decode `n` value records. -/
noncomputable def decVals (n : Nat) : Nat → List (Nat × Bool × Nat) :=
  Nat.rec (motive := fun _ => Nat → List (Nat × Bool × Nat)) (fun _ => [])
    (fun _ ih x =>
      (Nat.land x 4095, Nat.beq (Nat.land (Nat.shiftRight x 12) 1) 1,
        Nat.land (Nat.shiftRight x 32) (Nat.sub (Nat.shiftLeft 1 (Nat.land (Nat.shiftRight x 13) 524287)) 1)) ::
      ih (Nat.shiftRight x (Nat.add 32 (Nat.land (Nat.shiftRight x 13) 524287)))) n

/-- Index checks of `n` value records (indices `≥ lo`, strictly increasing, `< hi`). Returns `1 +` the next
admissible index, or `0` on failure. -/
noncomputable def valsOk (hi : Nat) (n : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun lo _ => Nat.add lo 1)
    (fun _ ih lo x =>
      Bool.rec 0 (ih (Nat.add (Nat.land x 4095) 1) (Nat.shiftRight x (Nat.add 32 (Nat.land (Nat.shiftRight x 13) 524287))))
        (Nat.ble lo (Nat.land x 4095) && Nat.blt (Nat.land x 4095) hi)) n

/-! ## Vectors (chunk sequences) -/

/-- Decode chunks `c, …, c+n-1` of a polynomial vector. -/
noncomputable def decPolyVec (R : Nat) (ch : Nat → Nat) (n : Nat) : Nat → List (Nat × Bool × Nat) :=
  Nat.rec (motive := fun _ => Nat → List (Nat × Bool × Nat)) (fun _ => [])
    (fun _ ih c => decPolys R (Nat.land (ch c) 255) (Nat.shiftRight (ch c) 8) ++ ih (Nat.add c 1)) n

/-- Header checks of a polynomial vector (chunks `c, …`); `lo1 = 1 +` lower bound, `0` = failure. -/
noncomputable def polyVecOk (Lmax wmax hi : Nat) (ch : Nat → Nat) (n : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ lo1 => lo1)
    (fun _ ih c lo1 =>
      Bool.rec 0 (ih (Nat.add c 1) (polysOk Lmax wmax hi (Nat.land (ch c) 255) (Nat.sub lo1 1) (Nat.shiftRight (ch c) 8)))
        (Nat.ble 1 lo1)) n

/-- Decode chunks `c, …, c+n-1` of a value vector. -/
noncomputable def decValVec (ch : Nat → Nat) (n : Nat) : Nat → List (Nat × Bool × Nat) :=
  Nat.rec (motive := fun _ => Nat → List (Nat × Bool × Nat)) (fun _ => [])
    (fun _ ih c => decVals (Nat.land (ch c) 255) (Nat.shiftRight (ch c) 8) ++ ih (Nat.add c 1)) n

/-- Index checks of a value vector (chunks `c, …`); `lo1 = 1 +` lower bound, `0` = failure. -/
noncomputable def valsOkVec (hi : Nat) (ch : Nat → Nat) (n : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ lo1 => lo1)
    (fun _ ih c lo1 =>
      Bool.rec 0 (ih (Nat.add c 1) (valsOk hi (Nat.land (ch c) 255) (Nat.sub lo1 1) (Nat.shiftRight (ch c) 8)))
        (Nat.ble 1 lo1)) n

/-! ## Main leaf -/

/-- `ys[p] += (σ, m) · e` for the entries `e` of the sparse `row` (positions relative to `pos`). -/
noncomputable def addRow (σ : Bool) (m : Nat) (ys : List (Nat × Nat)) :
    List (Nat × Bool × Nat) → Nat → List (Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Bool × Nat) → Nat → List (Nat × Nat)) (fun _ _ => [])
    (fun y ys' ih row pos =>
      List.rec (motive := fun _ => List (Nat × Nat)) (y :: ys')
        (fun e es _ =>
          Bool.rec (y :: ih (e :: es) (Nat.add pos 1))
            (Bool.rec (Nat.add y.1 (Nat.mul m e.2.2), y.2) (y.1, Nat.add y.2 (Nat.mul m e.2.2)) (xor σ e.2.1)
              :: ih es (Nat.add pos 1))
            (Nat.beq e.1 pos)) row) ys

/-- Column `k`: for the rows `i` (from `i`) with `N_ik ≠ 0`, `Y_i += (N_ik Γ_k) · Hs_k`. -/
noncomputable def walkRows (gs : Bool) (gm : Nat) (hs : List (Nat × Bool × Nat)) (i0 : Nat)
    (Y : List (List (Nat × Nat))) : List (Nat × Bool × Nat) → Nat → List (List (Nat × Nat)) :=
  List.rec (motive := fun _ => List (Nat × Bool × Nat) → Nat → List (List (Nat × Nat))) (fun _ _ => [])
    (fun y Ys ih col i =>
      List.rec (motive := fun _ => List (List (Nat × Nat))) (y :: Ys)
        (fun e es _ =>
          Bool.rec (y :: ih (e :: es) (Nat.add i 1))
            (addRow (xor gs e.2.1) (Nat.mul gm e.2.2) y hs i0 :: ih es (Nat.add i 1))
            (Nat.beq e.1 i)) col) Y

/-- Slice check of row `i`: `y[p] = [i = i0 + p] · (sQ)`. -/
noncomputable def sliceOk (i sq : Nat) (y : List (Nat × Nat)) (i0 : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih p => Bool.rec (Nat.beq e.1 e.2) (Nat.beq e.1 (Nat.add e.2 sq)) (Nat.beq i p) && ih (Nat.add p 1)) y i0

/-- All rows. -/
noncomputable def rowsOk (sq : Nat) (Y : List (List (Nat × Nat))) (i0 : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun y _ ih i => sliceOk i sq y i0 && ih (Nat.add i 1)) Y 0

/-- The data of one degree. -/
structure Tab where
  /-- radix bits -/
  R : Nat
  /-- dimension -/
  n : Nat
  /-- `N` column `k` (value records): chunk function and count -/
  nc : Nat → Nat → Nat
  nn : Nat → Nat
  /-- `Γ_k(B)` (value records, index `k`): chunk function and count; `s Q(B)` (positive) -/
  gc : Nat → Nat
  gn : Nat
  sq : Nat

/-- Stored column `k` of `N`. -/
noncomputable def ncolT (T : Tab) (k : Nat) : List (Nat × Bool × Nat) := decValVec (T.nc k) (T.nn k) 0

/-- One leaf: slice `[i0, i0 + len)` of the columns `i'`, `H` slice rows `k` given by `hc k`/`hn k`. -/
structure Slice where
  i0 : Nat
  len : Nat
  hc : Nat → Nat → Nat
  hn : Nat → Nat
  LH : Nat
  wH : Nat

/-- Process the columns `k` in the order of the `Γ` list (entries `(k, Γ_k(B))`): `Y_i += (N_ik Γ_k) H_k`
for the `H` slice row `k` (skipped when empty). -/
noncomputable def colsGo (T : Tab) (S : Slice) :
    List (Nat × Bool × Nat) → List (List (Nat × Nat)) → List (List (Nat × Nat)) :=
  List.rec (motive := fun _ => List (List (Nat × Nat)) → List (List (Nat × Nat))) (fun Y => Y)
    (fun g _ ih Y => ih ((fun hs => List.rec (motive := fun _ => List (List (Nat × Nat))) Y
        (fun _ _ _ => walkRows g.2.1 g.2.2 hs S.i0 Y (decValVec (T.nc g.1) (T.nn g.1) 0) 0) hs)
      (decPolyVec T.R (S.hc g.1) (S.hn g.1) 0)))

/-- `n` copies of `x`. -/
noncomputable def rep {α : Type} (x : α) (n : Nat) : List α :=
  Nat.rec (motive := fun _ => List α) [] (fun _ ih => x :: ih) n

/-- One-time header checks of the stored `N` columns and of `Γ` (indices strictly increasing, `< n`). -/
noncomputable def tabOk (T : Tab) : Bool :=
  Nat.ble 1 (valsOkVec T.n T.gc T.gn 0 1) &&
    Nat.rec (motive := fun _ => Bool) true (fun k ih => ih && Nat.ble 1 (valsOkVec T.n (T.nc k) (T.nn k) 0 1)) T.n

/-- Header checks of the `H` slice rows (`L ≤ LH`, `1 ≤ w ≤ wH`, indices strictly increasing in the slice). -/
noncomputable def sliceHdrOk (T : Tab) (S : Slice) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k ih => ih && Nat.ble 1 (polyVecOk S.LH S.wH (Nat.add S.i0 S.len) (S.hc k) (S.hn k) 0 (Nat.add S.i0 1))) T.n

/-- **Leaf check** of slice `S`: `Σ_k (N_ik Γ_k)(B) H_ki'(B) = [i = i'] sQ(B)` on the slice, plus its headers. -/
noncomputable def leafOk (T : Tab) (S : Slice) : Bool :=
  sliceHdrOk T S &&
    rowsOk T.sq (colsGo T S (decValVec T.gc T.gn 0) (rep (rep (0, 0) S.len) T.n)) S.i0

/-! ## The Γ/Q link (one-time leaf) -/

/-- Value of index `i` in a decoded list (`(false, 0)` if absent). -/
noncomputable def lookV (i : Nat) (l : List (Nat × Bool × Nat)) : Bool × Nat :=
  List.rec (motive := fun _ => Bool × Nat) (false, 0) (fun e _ ih => Bool.rec ih e.2 (Nat.beq e.1 i)) l

/-- Data of the Γ/Q link: `Γ_k` and `Q` as polynomial records, the denominators `dz` (index = id), the block
denominators `δ_b` (index = block), per output `k` a 512-bit info slot (32 per chunk): `λ_k` (bits 0–127),
`dq_k` (128–255), `Δc_k = S_r S_c rden_b` (256–319), dz id (320–335), block (336–351); and `s`. -/
structure GTab where
  gpc : Nat → Nat
  gpn : Nat
  qc : Nat → Nat
  qn : Nat
  dzc : Nat → Nat
  dzn : Nat
  blc : Nat → Nat
  bln : Nat
  info : Nat → Nat
  s : Nat
  /-- record bounds (for the ℓ1 bound of the identity): Γ, Q, dz, δ -/
  LG : Nat
  wG : Nat
  LQ : Nat
  wQ : Nat
  LD : Nat
  wD : Nat
  LB : Nat
  wB : Nat

/-- Info slot of output `k`. -/
def GTab.inf (G : GTab) (k : Nat) : Nat := fld (G.info (Nat.shiftRight k 5)) (Nat.mul 512 (Nat.land k 31)) 512

/-- `λ_k Δc_k Γ_k(B) dz_k(B) δ_b(B)² = s dq_k Q(B)` for the outputs `k` of the list `gl` (Γ records decoded), with
`dq_k ≥ 1` and the per-output coefficient bound `2 (λ_k Δc_k kg + s dq_k kq) < bnd` (`kg`, `kq`: ℓ1 bounds of
`Γ dz δ²` and `Q` from the record headers, `bnd = 2^R`). -/
noncomputable def gIdOk (G : GTab) (kg kq bnd : Nat) (qv : Bool × Nat) (dz bl : List (Nat × Bool × Nat)) :
    List (Nat × Bool × Nat) → Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun g _ ih =>
      (fun x d b =>
        Bool.rec
          (Nat.beq (Nat.mul (Nat.mul (Nat.mul (fld x 0 128) (fld x 256 64)) (Nat.mul g.2.2 d.2)) (Nat.mul b.2 b.2))
            (Nat.mul (Nat.mul G.s (fld x 128 128)) qv.2))
          false (xor qv.1 (xor g.2.1 d.1)) &&
        Nat.ble 1 (fld x 128 128) &&
        Nat.blt (Nat.mul 2 (Nat.add (Nat.mul (Nat.mul (fld x 0 128) (fld x 256 64)) kg)
          (Nat.mul (Nat.mul G.s (fld x 128 128)) kq))) bnd)
        (G.inf g.1) (lookV (fld (G.inf g.1) 320 16) dz) (lookV (fld (G.inf g.1) 336 16) bl) && ih)

/-- ℓ1 bound `L · 2^(w-1)` of a record with header bounds `L`, `w`. -/
def recBound (L w : Nat) : Nat := Nat.mul L (Nat.shiftLeft 1 (Nat.sub w 1))

/-- Equality of two decoded lists of `(index, sign, magnitude)`. -/
noncomputable def listEq : List (Nat × Bool × Nat) → List (Nat × Bool × Nat) → Bool :=
  List.rec (motive := fun _ => List (Nat × Bool × Nat) → Bool)
    (fun l => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l)
    (fun e _ ih l => List.rec (motive := fun _ => Bool) false
      (fun f fs _ => Nat.beq e.1 f.1 && Bool.rec (not f.2.1) f.2.1 e.2.1 && Nat.beq e.2.2 f.2.2 && ih fs) l)

/-- **Γ/Q link**: headers of all records, the stored `Γ_k(B)` values equal the records, `sQ(B)` equals `s` times
the `Q` record (positive), the `Γ` list has `n` entries (indices `< n`, increasing: every output has a `Γ_k`), and the
`Γ` identity at `2^R` with its coefficient bound. -/
noncomputable def gLinkOk (T : Tab) (G : GTab) : Bool :=
  Nat.ble 1 (polyVecOk G.LG G.wG T.n G.gpc G.gpn 0 1) && Nat.ble 1 (polyVecOk G.LQ G.wQ 1 G.qc G.qn 0 1) &&
  Nat.ble 1 (polyVecOk G.LD G.wD 4096 G.dzc G.dzn 0 1) && Nat.ble 1 (polyVecOk G.LB G.wB 4096 G.blc G.bln 0 1) &&
  listEq (decPolyVec T.R G.gpc G.gpn 0) (decValVec T.gc T.gn 0) &&
  Nat.beq (List.length (decPolyVec T.R G.gpc G.gpn 0)) T.n &&
  (fun qv => Bool.rec false (Nat.beq (Nat.mul G.s qv.2) T.sq) (not qv.1) &&
      gIdOk G (Nat.mul (Nat.mul (recBound G.LG G.wG) (recBound G.LD G.wD))
          (Nat.mul (recBound G.LB G.wB) (recBound G.LB G.wB))) (recBound G.LQ G.wQ) (Nat.shiftLeft 1 T.R) qv
        (decPolyVec T.R G.dzc G.dzn 0) (decPolyVec T.R G.blc G.bln 0) (decPolyVec T.R G.gpc G.gpn 0))
    (lookV 0 (decPolyVec T.R G.qc G.qn 0))

/-! ## The N link (canonical columns; one-time leaves)

Tag codes `x + 32 y + 1024 z`. Per output `k`: `oinfo k` = block (bits 0–7), `r` (8–15), `c` (16–23), `mult`
(24–31); κ column `(b, r)`: polynomial records indexed by the raw row `u` (chunks `kc b r`, count `kn b r`);
raw tag codes `rt b u` (bits 0–14 code, bit 15 the standard `Q` flag); `F0/F1` raw coefficients: `zt b u v`
= packed terms (count in bits 0–7, then 32-bit terms: code (15 bits), sign (1), magnitude (16)); retained tag
code of row `i`: `rtag i`. -/

/-- Raw-tensor terms `(code, sign, |z|)` of block `b` at raw rows `(u, v)`: m0Plus (`b = 2`): `t_u + t_v`
with `z = 1`; m0Standard (`b = 3`): `81 ×` the terms of `rawStandardCoordinates (p ∧ q) (p ∨ q)` shifted by
`t_u + t_v`; `F0/F1`: the packed list `zt b u v`. -/
noncomputable def zterms (rt : Nat → Nat → Nat) (zt : Nat → Nat → Nat → Nat) (b u v : Nat) :
    List (Nat × Bool × Nat) :=
  (fun cu cv =>
    (fun base => Bool.rec
      (Bool.rec
        (Nat.rec (motive := fun _ => Nat → List (Nat × Bool × Nat)) (fun _ => [])
          (fun _ ih x => (Nat.land x 32767, Nat.beq (Nat.land (Nat.shiftRight x 15) 1) 1,
              Nat.land (Nat.shiftRight x 16) 65535) :: ih (Nat.shiftRight x 32))
          (Nat.land (zt b u v) 255) (Nat.shiftRight (zt b u v) 8))
        [(base, false, 1)] (Nat.beq b 2))
      -- m0Standard: p ∧ q: 4/81 X0^4 - 8/27 X0^2 X1 + 4/9 X1^2; p ∨ q: 4/27 X0^3 - 2/3 X0 X1 + 2 X2;
      -- otherwise 4/9 X0^2 - 4/3 X1 (times 81)
      (Bool.rec
        (Bool.rec [(Nat.add base 2, false, 36), (Nat.add base 32, true, 108)]
          [(Nat.add base 3, false, 12), (Nat.add base 33, true, 54), (Nat.add base 1024, false, 162)]
          (Nat.beq (Nat.lor (Nat.shiftRight cu 15) (Nat.shiftRight cv 15)) 1))
        [(Nat.add base 4, false, 4), (Nat.add base 34, true, 24), (Nat.add base 64, false, 36)]
        (Nat.beq (Nat.land (Nat.shiftRight cu 15) (Nat.shiftRight cv 15)) 1))
      (Nat.beq b 3))
    (Nat.add (Nat.land cu 32767) (Nat.land cv 32767)))
  (rt b u) (rt b v)

/-- Not a retained tag of degree `D`: weight `x + 2y + 3z > D`, or `(0,0,0)`, or `(2,0,0)`. -/
def notRetained (D code : Nat) : Bool :=
  Nat.blt D (Nat.add (Nat.add (Nat.land code 31) (Nat.mul 2 (Nat.land (Nat.shiftRight code 5) 31)))
    (Nat.mul 3 (Nat.shiftRight code 10))) || Nat.beq code 0 || Nat.beq code 2

/-- Add `(σ, m)` to the accumulator entry with tag code `c` of `acc` (entries `(code, p, q)`); `none` if absent. -/
noncomputable def accAdd (c : Nat) (σ : Bool) (m : Nat) :
    List (Nat × Nat × Nat) → Option (List (Nat × Nat × Nat)) :=
  List.rec (motive := fun _ => Option (List (Nat × Nat × Nat))) none
    (fun e es ih => Bool.rec (Option.rec none (fun l => some (e :: l)) ih)
      (some (Bool.rec (e.1, Nat.add e.2.1 m, e.2.2) (e.1, e.2.1, Nat.add e.2.2 m) σ :: es)) (Nat.beq e.1 c))

/-- Accumulate the contributions `mult · z · κ_u κ_v` of one raw pair. -/
noncomputable def accTerms (D mult : Nat) (s1 : Bool) (m1 : Nat) :
    List (Nat × Bool × Nat) → List (Nat × Nat × Nat) → Option (List (Nat × Nat × Nat)) :=
  List.rec (motive := fun _ => List (Nat × Nat × Nat) → Option (List (Nat × Nat × Nat))) (fun acc => some acc)
    (fun t _ ih acc =>
      Option.rec (Bool.rec none (ih acc) (notRetained D t.1)) (fun acc' => ih acc')
        (accAdd t.1 (xor s1 t.2.1) (Nat.mul (Nat.mul mult t.2.2) m1) acc))

/-- Data of the N link. -/
structure LTab where
  D : Nat
  oinfo : Nat → Nat
  kc : Nat → Nat → Nat → Nat
  kn : Nat → Nat → Nat
  rt : Nat → Nat → Nat
  zt : Nat → Nat → Nat → Nat
  rtag : Nat → Nat

/-- Contributions of raw row `u` (sign `s1`, magnitude `m1`) with all `v` of the κ column `kcl`. -/
noncomputable def accV (L : LTab) (mult b u : Nat) (s1 : Bool) (m1 : Nat) :
    List (Nat × Bool × Nat) → List (Nat × Nat × Nat) → Option (List (Nat × Nat × Nat)) :=
  List.rec (motive := fun _ => List (Nat × Nat × Nat) → Option (List (Nat × Nat × Nat))) (fun acc => some acc)
    (fun v _ ih acc => Option.rec none (fun a => ih a)
      (accTerms L.D mult (xor s1 v.2.1) (Nat.mul m1 v.2.2) (zterms L.rt L.zt b u v.1) acc))

/-- All pairs `(u, v)` of the κ columns `kr × kcl`. -/
noncomputable def accU (L : LTab) (mult b : Nat) (kcl : List (Nat × Bool × Nat)) :
    List (Nat × Bool × Nat) → List (Nat × Nat × Nat) → Option (List (Nat × Nat × Nat)) :=
  List.rec (motive := fun _ => List (Nat × Nat × Nat) → Option (List (Nat × Nat × Nat))) (fun acc => some acc)
    (fun u _ ih acc => Option.rec none (fun a => ih a) (accV L mult b u.1 u.2.1 u.2.2 kcl acc))

/-- Stored entries `(i, s, m)` against the accumulators `(code, p, q)`: `±m = p - q`. -/
noncomputable def colOk : List (Nat × Bool × Nat) → List (Nat × Nat × Nat) → Bool :=
  List.rec (motive := fun _ => List (Nat × Nat × Nat) → Bool)
    (fun acc => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) acc)
    (fun e _ ih acc => List.rec (motive := fun _ => Bool) false
      (fun a as _ => Bool.rec (Nat.beq a.2.1 (Nat.add a.2.2 e.2.2)) (Nat.beq a.2.2 (Nat.add a.2.1 e.2.2)) e.2.1 &&
        ih as) acc)

/-- Initial accumulators: the tag codes of the stored rows. -/
noncomputable def acc0 (L : LTab) (l : List (Nat × Bool × Nat)) : List (Nat × Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat × Nat)) [] (fun e _ ih => (L.rtag e.1, 0, 0) :: ih) l

/-- N link of output `k`. -/
noncomputable def colLinkOk (T : Tab) (L : LTab) (k : Nat) : Bool :=
  (fun oi => (fun b r c mult =>
      Option.rec false (fun a => colOk (ncolT T k) a)
        (accU L mult b (decPolyVec T.R (L.kc b c) (L.kn b c) 0) (decPolyVec T.R (L.kc b r) (L.kn b r) 0)
          (acc0 L (ncolT T k))))
    (Nat.land oi 255) (Nat.land (Nat.shiftRight oi 8) 255) (Nat.land (Nat.shiftRight oi 16) 255)
    (Nat.land (Nat.shiftRight oi 24) 255))
  (L.oinfo k)

/-- One-time header checks of the κ columns `(b, r)`, `b < 4`, `r < 256` (`L ≤ LK`, `1 ≤ w ≤ wK`, raw rows strictly
increasing and `< mK`), and `block < 4` for the outputs `k < n`. -/
noncomputable def kapHdrOk (L : LTab) (n LK wK mK : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun b ih => ih &&
    Nat.rec (motive := fun _ => Bool) true
      (fun r ih2 => ih2 && Nat.ble 1 (polyVecOk LK wK mK (L.kc b r) (L.kn b r) 0 1)) 256) 4 &&
  Nat.rec (motive := fun _ => Bool) true (fun k ih => ih && Nat.blt (Nat.land (L.oinfo k) 255) 4) n

/-- **N link leaf**: outputs `k0, …, k0 + m - 1`. -/
noncomputable def linkOk (T : Tab) (L : LTab) (m k0 : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true) (fun _ ih k => colLinkOk T L k && ih (Nat.add k 1)) m k0

end ThomsonCompact.Fixed
