/-!
# F3 kernel: correction bounds on a height box (Init only)

Bit-exact with `tools/reference/floor_lx.py`. All arithmetic is on `Nat`. A signed packed vector is a pair
`(P, N)` of base-`2^W` digit vectors with value `slot P k - slot N k`. Hot loops use explicit recursors.

Height box `a = (mc + y)/2^hb`, `|y| ≤ Y`, global homogenisation degree `n`. With `z = mc + 2^W` (packed
`mc + X`), `V l = z^l 2^(hb(n-l))` packs `C(l,k) mc^(l-k) 2^(hb(n-l))`, so `Σ_l h_l V l` packs the exact Taylor
coefficients of `2^(hb n) h((mc+y)/2^hb)` in `y`.

Records (sign-magnitude slots `2|x| + [x < 0]`):
* entry (`H_jm`): bits `0..8` slot width `w`, `8..16` length `L`, `16..32` input index `m`, then `L` slots;
* denominator (`dz_j`, `d_j = dz_j / dq_j`): bits `0..8` width, `8..16` length, then the slots;
* column: slot `m` (width `wc`) holds `W_m`;
* row header: `λ_j + 2^128 dq_j + 2^256 u_j + 2^272 v_j + 2^288 (degree of dz_j)`.
-/

namespace ThomsonCompact.Floor

/-! ## Basic `Nat` helpers -/

def mask (w : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 w) 1

def slot (w x i : Nat) : Nat := Nat.land (Nat.shiftRight x (Nat.mul w i)) (mask w)

/-- `|a - b|` -/
def adiff (a b : Nat) : Nat := Nat.add (Nat.sub a b) (Nat.sub b a)

/-- `⌈a / b⌉` -/
def cdiv (a b : Nat) : Nat := Nat.div (Nat.add a (Nat.sub b 1)) b

/-- `Σ_{k<n} |slot_k P - slot_k N| Y^k` -/
noncomputable def magD (W mW Y : Nat) (n : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => 0)
    (fun _ ih P N => Nat.add (adiff (Nat.land P mW) (Nat.land N mW))
      (Nat.mul Y (ih (Nat.shiftRight P W) (Nat.shiftRight N W)))) n

/-! ## Shift tables -/

/-- `[z^l 2^(hb(n-l)) | l = i, …, i + r - 1]` given `pz = z^i` -/
noncomputable def vGo (z hb n : Nat) (r : Nat) : Nat → Nat → List Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → List Nat) (fun _ _ => [])
    (fun _ ih pz i => Nat.shiftLeft pz (Nat.mul hb (Nat.sub n i)) :: ih (Nat.mul pz z) (Nat.succ i)) r

/-- `V l`, `l = 0 … n` -/
noncomputable def vlist (z hb n : Nat) : List Nat := vGo z hb n (Nat.succ n) 1 0

/-! ## Entry shifts: `(J⁺, J⁻)` with `J = J⁺ - J⁻` packed -/

noncomputable def shiftGo (w mw : Nat) : List Nat → Nat → Nat → Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat × Nat) (fun _ jp jn => (jp, jn))
    (fun vl _ ih c jp jn =>
      ih (Nat.shiftRight c w)
        (Bool.rec (Nat.add jp (Nat.mul (Nat.shiftRight (Nat.land c mw) 1) vl)) jp
          (Nat.beq (Nat.land c 1) 1))
        (Bool.rec jn (Nat.add jn (Nat.mul (Nat.shiftRight (Nat.land c mw) 1) vl))
          (Nat.beq (Nat.land c 1) 1)))

/-- Header fields of a record. -/
def recW (e : Nat) : Nat := Nat.land e 255
def recL (e : Nat) : Nat := Nat.land (Nat.shiftRight e 8) 255
def recM (e : Nat) : Nat := Nat.land (Nat.shiftRight e 16) 65535

/-- `(m, J⁺, J⁻)` of an entry record (the coefficient slots start at bit 32). -/
noncomputable def entryShift (V : List Nat) (e : Nat) : Nat × Nat × Nat :=
  (recM e, shiftGo (recW e) (mask (recW e)) V (Nat.shiftRight e 32) 0 0)

noncomputable def rowShift (V : List Nat) (row : List Nat) : List (Nat × Nat × Nat) :=
  List.rec (motive := fun _ => List (Nat × Nat × Nat)) [] (fun e _ ih => entryShift V e :: ih) row

/-! ## Column contraction `N = Σ_m W_m J_m` (packed) -/

/-- Accumulator form: `colAt m` is the sign-magnitude slot `2|W_m| + [W_m < 0]` of the column. -/
noncomputable def contractGo (colAt : Nat → Nat) : List (Nat × Nat × Nat) → Nat → Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat × Nat) (fun np nn => (np, nn))
    (fun en _ ih np nn =>
      Bool.rec
        (ih (Nat.add np (Nat.mul (Nat.shiftRight (colAt en.1) 1) en.2.1))
            (Nat.add nn (Nat.mul (Nat.shiftRight (colAt en.1) 1) en.2.2)))
        (ih (Nat.add np (Nat.mul (Nat.shiftRight (colAt en.1) 1) en.2.2))
            (Nat.add nn (Nat.mul (Nat.shiftRight (colAt en.1) 1) en.2.1)))
        (Nat.beq (Nat.land (colAt en.1) 1) 1))

noncomputable def contract (colAt : Nat → Nat) (ent : List (Nat × Nat × Nat)) : Nat × Nat :=
  contractGo colAt ent 0 0

/-! ## Denominators: exact shift, separation from zero, inverse jets and their remainder -/

/-- Signed value of slot `k` of `(P, N)` as an `Int` (small loops only). -/
def sval (W P N k : Nat) : Int := Int.subNatNat (slot W P k) (slot W N k)

/-- Formal inverse `I` of `D` to order `K` at scale `2^B` (floor division; any integers are sound). -/
def invJets (W P N B : Nat) (K : Nat) : List Int :=
  (Nat.rec (motive := fun _ => List Int) []
    (fun k ih => ih ++ [Int.fdiv ((if k = 0 then (2 : Int) ^ B else 0) -
        (List.range k).foldl (fun s t => s + sval W P N (k - t) * ih.getD t 0) 0) (sval W P N 0)]) (Nat.succ K))

/-- Pack a list of integers into `(P, N)` with slot width `W`. -/
def packInts (W : Nat) : List Int → Nat × Nat
  | [] => (0, 0)
  | x :: xs => let r := packInts W xs
      (Nat.add x.toNat (Nat.shiftLeft r.1 W), Nat.add (-x).toNat (Nat.shiftLeft r.2 W))

/-- Per denominator: `(I⁺, I⁻, B, rI, dmin, degree)`, or `none` if not separated from zero. -/
noncomputable def denomData (W Y K hb mc : Nat) (d : Nat) : Option (Nat × Nat × Nat × Nat × Nat × Nat) :=
  let nd := Nat.sub (recL d) 1
  let V := vlist (Nat.add mc (Nat.shiftLeft 1 W)) hb nd
  let D := shiftGo (recW d) (mask (recW d)) V (Nat.shiftRight d 16) 0 0
  let mW := mask W
  let d0 := adiff (Nat.land D.1 mW) (Nat.land D.2 mW)
  let rest := Nat.mul Y (magD W mW Y nd (Nat.shiftRight D.1 W) (Nat.shiftRight D.2 W))
  let B := Nat.add (Nat.log2 d0) 261
  let I := packInts W (invJets W D.1 D.2 B K)
  let Rp := Nat.add (Nat.shiftLeft 1 B) (Nat.add (Nat.mul D.1 I.2) (Nat.mul D.2 I.1))
  let Rn := Nat.add (Nat.mul D.1 I.1) (Nat.mul D.2 I.2)
  let dmin := Nat.sub d0 rest
  Bool.rec none (some (I.1, I.2, B, cdiv (magD W mW Y (Nat.add nd (Nat.succ K)) Rp Rn) dmin, dmin, nd))
    (Nat.blt rest d0)

/-! ## Young bound -/

/-- `Σ_q M_pq w_q` for each row `p` -/
def matVec (M : List (List Nat)) (w : List Nat) : List Nat :=
  M.map (fun r => (r.zip w).foldl (fun s x => Nat.add s (Nat.mul x.1 x.2)) 0)

/-- `max_p ⌈(M w)_p / w_p⌉` -/
def youngG (M : List (List Nat)) (w : List Nat) : Nat :=
  ((matVec M w).zip w).foldl (fun g x => Nat.max g (cdiv x.1 x.2)) 0

/-- symmetric part `min(M, Mᵀ)` -/
def symMin (M : List (List Nat)) : List (List Nat) :=
  (List.range M.length).map fun p => (List.range M.length).map fun q =>
    Nat.min ((M.getD p []).getD q 0) ((M.getD q []).getD p 0)

/-- Weight iteration (12 rounds) of `cellcheck.weighted_bound`; returns the best weights (unverified heuristic). -/
noncomputable def youngW (M : List (List Nat)) : List Nat :=
  let mx := (M.map fun r => r.foldl Nat.add 0).foldl Nat.max 0
  (Nat.rec (motive := fun _ => List Nat × List Nat × Nat)
    (List.replicate M.length 65536, List.replicate M.length 65536, youngG M (List.replicate M.length 65536))
    (fun _ st =>
      let img := matVec M st.1
      let prop := (img.zip st.1).map fun x => Nat.add x.1 (Nat.mul mx x.2)
      let nz := prop.foldl Nat.max 0
      let w' := prop.map fun x => Nat.max 1 (Nat.div (Nat.shiftLeft x 16) nz)
      let g' := youngG M w'
      Bool.rec (w', st.2.1, st.2.2) (w', w', g') (Nat.blt g' st.2.2)) 11).2.1

/-- Young bound of a nonnegative matrix: `(Γ, w)` with `Σ_q min(M,Mᵀ)_pq w_q ≤ Γ w_p`. -/
noncomputable def young (M : List (List Nat)) : Nat :=
  let S := symMin M
  youngG S (youngW S)

/-! ## Block bounds -/

/-- Per-row data of a corrected block. -/
structure RowD where
  lam : Nat
  dq : Nat
  u : Nat
  v : Nat
  nd : Nat
  Ip : Nat
  In : Nat
  B : Nat
  rI : Nat
  dmin : Nat
  ent : List (Nat × Nat × Nat)
  deriving Inhabited

/-- Row header fields. -/
def hdrLam (h : Nat) : Nat := Nat.land h (mask 128)
def hdrDq (h : Nat) : Nat := Nat.land (Nat.shiftRight h 128) (mask 128)
def hdrU (h : Nat) : Nat := Nat.land (Nat.shiftRight h 256) 65535
def hdrV (h : Nat) : Nat := Nat.land (Nat.shiftRight h 272) 65535

/-- Row data from the row header, the denominator record and the entry records (`none`: denominator fails). -/
noncomputable def rowData (W Y K hb mc : Nat) (V : List Nat) (hdr den : Nat) (row : List Nat) :
    Option RowD :=
  (denomData W Y K hb mc den).map fun d =>
    ⟨hdrLam hdr, hdrDq hdr, hdrU hdr, hdrV hdr, d.2.2.2.2.2, d.1, d.2.1, d.2.2.1, d.2.2.2.1, d.2.2.2.2.1,
     rowShift V row⟩

/-- Reduced fraction `a / b` as `(a / g, b / g)`. -/
def reduce (a b : Nat) : Nat × Nat := (Nat.div a (Nat.gcd a b), Nat.div b (Nat.gcd a b))

/-- Scale `σ_j = dq 2^(hb nd) num / (λ den 2^(hb n + Sc + B))` of each row, reduced. -/
def sigmas (hb n Sc num den : Nat) (rs : List RowD) : List (Nat × Nat) :=
  rs.map fun r => reduce (Nat.mul (Nat.shiftLeft r.dq (Nat.mul hb r.nd)) num)
    (Nat.shiftLeft (Nat.mul r.lam den) (Nat.add (Nat.add (Nat.mul hb n) Sc) r.B))

/-- Common denominator `sd` and numerators `sn_j = σ_j sd`. -/
def commonDen (sg : List (Nat × Nat)) : Nat × List Nat :=
  let sd := sg.foldl (fun l x => Nat.div (Nat.mul l x.2) (Nat.gcd l x.2)) 1
  (sd, sg.map fun x => Nat.mul x.1 (Nat.div sd x.2))

/-- Signed `Zi` entry. -/
def zget (Z : List (List Int)) (p u : Nat) : Int := (Z.getD p []).getD u 0

/-- Congruence coefficients `Tz_pq,j sn_j` for all `p ≤ q`, aligned with the rows. -/
def congCoeffs (Z : List (List Int)) (n : Nat) (rs : List RowD) (sn : List Nat) : List (List Int) :=
  ((List.range n).flatMap fun p => (List.range (n - p)).map fun i => (p, p + i)).map fun pq =>
    (rs.zip sn).map fun x =>
      (zget Z pq.1 x.1.u * zget Z pq.2 x.1.v +
        (if x.1.u = x.1.v then 0 else zget Z pq.1 x.1.v * zget Z pq.2 x.1.u)) * (x.2 : Int)

/-- `(negative?, |x|)` -/
noncomputable def sgnAbs (x : Int) : Bool × Nat := Int.rec (fun n => (false, n)) (fun n => (true, Nat.succ n)) x

/-- `(G⁺, G⁻, Err) = Σ_j c_j (P⁺_j, P⁻_j)` (signed) and `Σ_j |c_j| eps_j` (accumulator form). -/
noncomputable def congGo : List (Int × (Nat × Nat × Nat)) → Nat → Nat → Nat → Nat × Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat × Nat × Nat) (fun gp gn er => (gp, gn, er))
    (fun x _ ih gp gn er =>
      Bool.rec (ih (Nat.add gp (Nat.mul (sgnAbs x.1).2 x.2.1)) (Nat.add gn (Nat.mul (sgnAbs x.1).2 x.2.2.1))
          (Nat.add er (Nat.mul (sgnAbs x.1).2 x.2.2.2)))
        (ih (Nat.add gp (Nat.mul (sgnAbs x.1).2 x.2.2.1)) (Nat.add gn (Nat.mul (sgnAbs x.1).2 x.2.1))
          (Nat.add er (Nat.mul (sgnAbs x.1).2 x.2.2.2)))
        (sgnAbs x.1).1)

noncomputable def congEntry (cs : List Int) (ps : List (Nat × Nat × Nat)) : Nat × Nat × Nat :=
  congGo (cs.zip ps) 0 0 0

/-- Products `P = N ⋆ I` and `eps = |N|(Y) rI` of every row for one column. -/
noncomputable def rowProducts (W mW Y n : Nat) (colAt : Nat → Nat) (rs : List RowD) : List (Nat × Nat × Nat) :=
  rs.map fun r =>
    let c := contract colAt r.ent
    (Nat.add (Nat.mul c.1 r.Ip) (Nat.mul c.2 r.In), Nat.add (Nat.mul c.1 r.In) (Nat.mul c.2 r.Ip),
     Nat.mul (magD W mW Y (Nat.succ n) c.1 c.2) r.rI)

/-- Symmetric matrix from the upper-triangle list (row-major `p ≤ q`). -/
def symFromUpper (n : Nat) (up : List Nat) : List (List Nat) :=
  (List.range n).map fun p => (List.range n).map fun q =>
    up.getD (if p ≤ q then p * n - p * (p - 1) / 2 + (q - p) else q * n - q * (q - 1) / 2 + (p - q)) 0

/-- Young bound (scale `2^-YSC`) of `Z M(a) Zᵀ` for one column, uniformly on the box. -/
noncomputable def columnBound (W Y YSC n K nb : Nat) (colAt : Nat → Nat) (sd : Nat) (cc : List (List Int))
    (rs : List RowD) : Nat :=
  let mW := mask W
  let ps := rowProducts W mW Y n colAt rs
  young (symFromUpper nb (cc.map fun cs =>
    let g := congEntry cs ps
    cdiv (Nat.shiftLeft (Nat.add (magD W mW Y (Nat.add (Nat.succ n) K) g.1 g.2.1) g.2.2) YSC) (Nat.shiftLeft sd 64)))

/-! ## Decoding small signed data -/

/-- `n` sign-magnitude slots of width `w` -/
def decodeSM (w : Nat) : Nat → Nat → List Int
  | 0, _ => []
  | n + 1, x => Int.subNatNat (Nat.shiftRight (Nat.land x (mask w)) 1)
      (Nat.mul (Nat.land x 1) (Nat.mul 2 (Nat.shiftRight (Nat.land x (mask w)) 1))) :: decodeSM w n (Nat.shiftRight x w)

/-- split a list into rows of length `n` -/
def toRows (n : Nat) : Nat → List Int → List (List Int)
  | 0, _ => []
  | r + 1, L => L.take n :: toRows n r (L.drop n)

/-! ## Error part -/

/-- `(u, v, E_j)` for one row (scale `2^-YSC`): structured target errors through the direction columns
`(colAt, num, den)` (value `W num / den`) with radii `herr` (scale `2^-S`) and the box radii `errAt m` (scale `2^-S`). -/
noncomputable def errorRow (W Y YSC S hb n : Nat) (errAt : Nat → Nat) (dirs : List ((Nat → Nat) × Nat × Nat))
    (herr : List Nat) (r : RowD) : Nat × Nat × Nat :=
  let mW := mask W
  let den0 := Nat.mul (Nat.shiftLeft r.lam (Nat.add S (Nat.mul hb n))) r.dmin
  let num0 := Nat.shiftLeft r.dq (Nat.add YSC (Nat.mul hb r.nd))
  let st := (dirs.zip herr).foldl (fun acc x =>
      let c := contract x.1.1 r.ent
      Nat.add acc (cdiv (Nat.mul (Nat.mul (Nat.mul x.2 num0) x.1.2.1) (magD W mW Y (Nat.succ n) c.1 c.2))
        (Nat.mul den0 x.1.2.2))) 0
  let bx := r.ent.foldl (fun acc en =>
      Nat.add acc (Nat.mul (errAt en.1) (magD W mW Y (Nat.succ n) en.2.1 en.2.2))) 0
  (r.u, r.v, Nat.add st (cdiv (Nat.mul num0 bx) den0))

/-- `E_pq = max {E_j : {u_j, v_j} = {p, q}}` -/
noncomputable def matFromRows (n : Nat) (es : List (Nat × Nat × Nat)) : List (List Nat) :=
  (List.range n).map fun p => (List.range n).map fun q =>
    es.foldl (fun m e => Bool.rec m (Nat.max m e.2.2)
      ((Nat.beq e.1 p && Nat.beq e.2.1 q) || (Nat.beq e.1 q && Nat.beq e.2.1 p))) 0

/-- `⌈|Z| E |Z|ᵀ / 2^64⌉` -/
def absCong (Z : List (List Int)) (E : List (List Nat)) : List (List Nat) :=
  let Za := Z.map fun r => r.map Int.natAbs
  let A := Za.map fun zr => (List.range Za.length).map fun v =>
    (zr.zip E).foldl (fun s x => Nat.add s (Nat.mul x.1 (x.2.getD v 0))) 0
  A.map fun ar => Za.map fun zq => cdiv ((ar.zip zq).foldl (fun s x => Nat.add s (Nat.mul x.1 x.2)) 0) (Nat.shiftLeft 1 64)

/-! ## Short metric -/

/-- `Σ_{j<n} f j` -/
def sumZ (n : Nat) (f : Nat → Int) : Int := Nat.rec (motive := fun _ => Int) 0 (fun j acc => acc + f j) n

/-- `Σ_{j<n} f j` -/
def sumN (n : Nat) (f : Nat → Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Nat.add acc (f j)) n

/-- `max_{j<n} f j` (`0` if `n = 0`) -/
def maxN (n : Nat) (f : Nat → Nat) : Nat := Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Nat.max acc (f j)) n

/-- entry `(i, j)` of a list-of-rows integer matrix -/
def zent (Z : List (List Int)) (i j : Nat) : Int := (Z.getD i []).getD j 0

/-- `Kz` (scale `2^-mb`) of a literal metric: diagonal exponents `ex`, strict lower entries `kl` (row major). -/
def kzent (bits mb : Nat) (ex kl : List Int) (i j : Nat) : Int :=
  if j < i then kl.getD (i * (i - 1) / 2 + j) 0 * (2 : Int) ^ (mb - bits)
  else if i = j then (2 : Int) ^ (Int.toNat ((mb : Int) + ex.getD i 0)) else 0

/-- `F = Zi Kz - 2^sc 1` (scale `2^-sc`, `sc = 32 + mb`) -/
def fent (Z : List (List Int)) (n bits mb : Nat) (ex kl : List Int) (sc i j : Nat) : Int :=
  sumZ n (fun l => zent Z i l * kzent bits mb ex kl l j) - (if i = j then (2 : Int) ^ sc else 0)

/-- `max_i Σ_j |F_ij + F_ji|` -/
def thetaNum (Z : List (List Int)) (n bits mb : Nat) (ex kl : List Int) (sc : Nat) : Nat :=
  maxN n fun i => sumN n fun j => (fent Z n bits mb ex kl sc i j + fent Z n bits mb ex kl sc j i).natAbs

end ThomsonCompact.Floor
