import ThomsonCompact.CoeffMap.Deg.Codec
import ThomsonCompact.CoeffMap.Prog
import ThomsonCompact.CoeffMap.MomentProg
import ThomsonCompact.CoeffMap.BSum
import ThomsonCompact.CoeffMap.Deg.Dot

/-!
# W0 block contributions of any degree: per-cell kernel programs (Init only; F2e)

For block `b` of the per-degree data `L : DegD`, height TM `A` and W0 Gram TMs `WT i j` of the block:

* rows of the column matrix (precise entries, as `CoeffMap.KRowsR`): scalar rows from the RF records
  (`recTMr = refresh (divR num den (1/den))`, shared inverses `denInvTab`), moment rows from the pivot ratios
  (`rhoTMr`, mirror `mP` of `momentP`);
* `pT`: the table of `P u v = (K W Kᵀ)ᵤᵥ` (`CoeffMap.Prog.pTabz`, z table, pivot-row symmetry);
* owner parts: the pairs `(u, v)` of a class are split by their *owner* `SumD.own` (`v` if row `v` is dense, else `u` if
  row `u` is dense, else `256 + u` for two pivot rows; per-cell dense-row mask `SumD.dm`) into per-cell ranges
  `[plo b h, plo b (h+1))` (`partsOk`), so that one leaf only evaluates the rows of its own dense owners (stage-P
  lookup `CoeffMap.Deg.StageZ.PS`) and pivot-pivot pairs (W0 entries only) form parts of their own; the owner never
  evaluates a row (rows at decoded indices would not be shared by the kernel);
* `qTM b k lo hi = Σ_{(u,v) ∈ class k, owner ∈ [lo,hi)} m(u,v) P u v` (`m = 1` on the diagonal, `2` off it);
* `pieceTM b g lo hi E = Σ_{(k,±m) ∈ E} (±m / den_b) Q_k^{[lo,hi)}` for the coefficient list `E = L.eTab (32 b + g)` of
  a coordinate (classes without pairs in the range are skipped).

Leaf checker `leafOk`: pieces `(b, g, h)`, `g0 ≤ g < g1`, at coordinates `r0 ≤ r < r1` are `ok` and match their
checkpoints (`CoeffMap.BSum.ckOk`, target order `n`). Sum checker `sumOkD`; per-cell check `denOkD` (denominators and
the owner partition). Soundness: `CoeffMap.Deg.ProgSound`. Bit-exact mirror: `CoeffMap/Deg/gen/mirror.py`.
-/

namespace ThomsonCompact.CoeffMap.Deg

open ThomsonCompact.Packed ThomsonCompact.CoeffMap

/-- `succAbove p i` on `ℕ`. -/
def sAb (p i : Nat) : Nat := if i < p then i else i + 1

/-- Rational coefficients of the moment pivot polynomial `momentP k j` (`√2`-free part of the mirror). -/
def momQd (k j : Nat) : List (Bool × Nat × Nat) := toQL (mP k j).r

namespace DegD

variable (L : DegD)

/-- The shared denominators at the height TM (each evaluated once per leaf). -/
noncomputable def denGTab (c : Ctx) (A : TM) : List TM :=
  mkList (fun d => hornerQ c A (L.denQ d)) L.nDen

/-- Shared denominator `d` at the height TM. -/
noncomputable def denGAt (c : Ctx) (A : TM) (d : Nat) : TM :=
  cond (Nat.blt d L.nDen) (listAt zeroTM (L.denGTab c A) d) (hornerQ c A (L.denQ d))

/-- Inverse TMs of the shared denominators at the height TM (each evaluated once per leaf). -/
noncomputable def denInvTab (c : Ctx) (A : TM) : List TM :=
  mkList (fun d => invN c 8 0 (hornerQ c A (L.denQ d))) L.nDen

/-- Shared inverse of denominator `d`. -/
noncomputable def denInvAt (c : Ctx) (A : TM) (d : Nat) : TM :=
  cond (Nat.blt d L.nDen) (listAt zeroTM (L.denInvTab c A) d) (invN c 8 0 (hornerQ c A (L.denQ d)))

/-- Record `k` at `A`: `refresh (divR num den (1/den))` (numerator as one dot product with the powers of `A`; shared
denominator and inverse tables). -/
noncomputable def recTMr (c : Ctx) (A : TM) (k : Nat) : TM :=
  refresh c (divR c (polyD c A (L.numQ k)) (L.denGAt c A (L.denIdx k)) (L.denInvAt c A (L.denIdx k)))

/-- Row `u` of scalar block `j` (record `0` is the exact `1`, record `1` the zero). -/
noncomputable def scalarRowr (c : Ctx) (A : TM) (j u : Nat) : List (Nat × Option TM) :=
  ((List.range (L.gdim (Nat.add L.dH j))).filter fun i => !(Nat.beq (L.colRec j i u) 1)).map fun i =>
    (i, if Nat.beq (L.colRec j i u) 0 then none else some (L.recTMr c A (L.colRec j i u)))

end DegD

/-- `-momentP k (succAbove p i) / momentP k p` at the height TM by the residual lemma. -/
noncomputable def rhoTMd (c : Ctx) (A : TM) (k p i : Nat) : TM :=
  refresh c (neg c (divR c (hornerQ c A (momQd k (sAb p i))) (hornerQ c A (momQd k p))
    (invN c 8 0 (hornerQ c A (momQd k p)))))

/-- Row `r` of moment block `k` (pivot `p`, `d` columns). -/
noncomputable def momentRowd (c : Ctx) (A : TM) (k p d r : Nat) : List (Nat × Option TM) :=
  if r = p then (List.range d).map fun i => (i, some (rhoTMd c A k p i))
  else [(if r < p then r else r - 1, none)]

/-! ## Contraction with row walks

Rows list `(j, e)` with strictly increasing `j`. Instead of indexed lookups (`O(j)` kernel steps each), a W row or a
z column is read along a row in one walk (`zipRow`); every table entry has literal indices (evaluated once). Dense rows use
one packed dot product per entry (`CoeffMap.Deg.Dot`); pivot rows read the table entry directly. -/

/-- `[(e, ws[j]) | (j, e) ∈ row]`, reading `ws` (the full list from index `k` on) in one walk. -/
noncomputable def zipRow (row : List (Nat × Option TM)) : List TM → Nat → List (Option TM × TM) :=
  List.rec (motive := fun _ => List TM → Nat → List (Option TM × TM)) (fun _ _ => [])
    (fun p _ ih ws k => (fun ws' => (p.2, ws'.headD zeroTM) :: ih ws'.tail (Nat.add p.1 1)) (ws.drop (Nat.sub p.1 k)))
    row

/-- `Σ_{(e, X)} e · X` (`none` is the exact `1`) as one packed dot product. -/
noncomputable def dotOpt (c : Ctx) (L : List (Option TM × TM)) : TM := dotTM c (L.map fun q => (entTM c q.1, q.2))

/-- Full rows of the W TMs: row `i` is `[WT i 0, …, WT i (n-1)]`. -/
noncomputable def wRowsD (WT : Nat → Nat → TM) (n : Nat) : List (List TM) :=
  mkList (fun i => mkList (fun j => WT i j) n) n

/-- `Z i v = Σ_{(j,e) ∈ row v} e · W i j` (W row `i` walked along row `v`; a pivot row `v = e_j` gives `W i j`). -/
noncomputable def zTMD (c : Ctx) (row : Nat → List (Nat × Option TM)) (wr : List (List TM)) (i v : Nat) : TM :=
  Option.casesOn (motive := fun _ => TM) (pivotOf (row v)) (dotOpt c (zipRow (row v) (listAt [] wr i) 0))
    (fun j => listAt zeroTM (listAt [] wr i) j)

/-- Z column `v`: for a dense row `v` the entries `zTMD i v` (one dot product each; the Kronecker batch `bdot` of
`CoeffMap.Deg.Dot` measured 2.5 s and 0.6 GB more per M1_even leaf); for a pivot row `v = e_j` the W row `j`
(`W` symmetric). -/
noncomputable def zColD (c : Ctx) (row : Nat → List (Nat × Option TM)) (wr : List (List TM)) (n v : Nat) : List TM :=
  Option.casesOn (motive := fun _ => List TM) (pivotOf (row v))
    (mkList (fun i => zTMD c row wr i v) n)
    (fun j => listAt [] wr j)

/-- The z columns: column `v < m` is `[Z 0 v, …, Z (n-1) v]`. -/
noncomputable def zColsD (c : Ctx) (row : Nat → List (Nat × Option TM)) (wr : List (List TM)) (n m : Nat) :
    List (List TM) :=
  mkList (fun v => zColD c row wr n v) m

/-- `P u v = (K W Kᵀ)ᵤᵥ`: z column `v` walked along row `u` (a pivot row `u = e_i` gives `Z i v`); for a pivot row
`v = e_j`, `Z j u` (W symmetric). -/
noncomputable def pTMD (c : Ctx) (row : Nat → List (Nat × Option TM)) (zc : List (List TM)) (u v : Nat) : TM :=
  Option.casesOn (motive := fun _ => TM) (pivotOf (row v))
    (Option.casesOn (motive := fun _ => TM) (pivotOf (row u)) (dotOpt c (zipRow (row u) (listAt [] zc v) 0))
      (fun i => listAt zeroTM (listAt [] zc v) i))
    (fun j => listAt zeroTM (listAt [] zc u) j)

/-- The table of all `pTMD u v`, `u, v < k`. -/
noncomputable def pTabD (c : Ctx) (row : Nat → List (Nat × Option TM)) (zc : List (List TM)) (k : Nat) :
    List (List TM) :=
  mkList (fun u => mkList (fun v => pTMD c row zc u v) k) k

namespace DegD

variable (L : DegD)

/-- Rows of block `b`. -/
noncomputable def blockRow (c : Ctx) (A : TM) (b : Nat) : Nat → List (Nat × Option TM) :=
  if b < L.dH then momentRowd c A b (L.piv b) (L.gdim b) else L.scalarRowr c A (b - L.dH)

/-- The table of `P u v = (K W Kᵀ)ᵤᵥ`, `u, v < rdim b` (W rows and z columns read along the rows, `pTMD`). -/
noncomputable def pT (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (b : Nat) : List (List TM) :=
  pTabD c (L.blockRow c A b) (zColsD c (L.blockRow c A b) (wRowsD WT (L.gdim b)) (L.gdim b) (L.rdim b)) (L.rdim b)

/-- The `P` lookup of block `b` from the computed table `pT` (the piece programs below take any `P` lookup). -/
noncomputable def pLook (c : Ctx) (A : TM) (WT : Nat → Nat → TM) (b : Nat) : Nat → Nat → TM :=
  fun u v => listAt zeroTM (listAt [] (L.pT c A WT b) u) v

end DegD

/-- Per-cell checkpoint data of the W0 sums (any degree). -/
structure SumD where
  /-- checkpoint scale shift: values at `2^-(S-F)` -/
  F : Nat
  /-- owner parts of block `b`: dense-row mask (bit `v` set iff row `v` is not a pivot row), number of parts,
  boundaries `plo b 0 = 0 ≤ … ≤ plo b (np b)` (16-bit slots of `pl b`) -/
  dm : Nat → Nat
  np : Nat → Nat
  pl : Nat → Nat
  /-- block ↦ slot widths `w_0 … w_n, w_e` (9-bit slots), record width, records per numeral -/
  lay : Nat → Nat
  rw : Nat → Nat
  per : Nat → Nat
  /-- numeral `c` of the records of pseudo-piece `pp = 32 (32 b + g) + h` -/
  chunk : Nat → Nat → Nat
  /-- final sums: widths, record width, records per numeral, numerals -/
  dLay : Nat
  dRw : Nat
  dPer : Nat
  dChunk : Nat → Nat

/-- Owner of the pair `(u, v)` of block `b`: `v` if row `v` is dense (`dm` bit set), else `u` if row `u` is dense,
else `256 + u` (pairs of two pivot rows: their own owner range, they only need W0 entries). Any mask is sound. -/
def SumD.own (sd : SumD) (b u v : Nat) : Nat :=
  cond (Nat.beq (Nat.land (Nat.shiftRight (sd.dm b) v) 1) 1) v
    (cond (Nat.beq (Nat.land (Nat.shiftRight (sd.dm b) u) 1) 1) u (Nat.add 256 u))

/-- The pair `p` belongs to the owner range `[lo, hi)`. -/
def SumD.inPart (sd : SumD) (b lo hi : Nat) (p : Nat × Nat) : Bool :=
  Nat.ble lo (sd.own b p.1 p.2) && Nat.blt (sd.own b p.1 p.2) hi

/-- Lower owner boundary of part `h` of block `b`. -/
def SumD.plo (sd : SumD) (b h : Nat) : Nat := slotAt 16 (sd.pl b) h

namespace DegD

variable (L : DegD)

/-- The pairs of class `k` of block `b` with owner in `[lo, hi)`. -/
def clsPart (sd : SumD) (b k lo hi : Nat) : List (Nat × Nat) :=
  (L.clsPairs b k).filter (sd.inPart b lo hi)

/-- `Σ_{(u,v) ∈ ps} m(u,v) P u v` (`m = 1` on the diagonal, `2` off it) from the `P` table of block `b`, as one dot
product. -/
noncomputable def qSum (c : Ctx) (PT : Nat → Nat → TM) (ps : List (Nat × Nat)) : TM :=
  dotTM c (ps.map fun p => (constI c (cond (Nat.beq p.1 p.2) 1 2), PT p.1 p.2))

/-- `(no pairs, Q_k^{[lo,hi)})` with `Q_k^{[lo,hi)} = Σ_{(u,v) ∈ class k, owner ∈ [lo,hi)} m(u,v) P u v`. -/
noncomputable def qEnt (c : Ctx) (PT : Nat → Nat → TM) (sd : SumD) (b k lo hi : Nat) : Bool × TM :=
  ((L.clsPart sd b k lo hi).isEmpty, qSum c PT (L.clsPart sd b k lo hi))

/-- The `Q` table of group `g` of block `b` (classes `glo b g + i`, `i < 16 ⌊len/16⌋ + 16`), owner range `[lo, hi)`,
in chunks of 16 (entry `i` is slot `i & 15` of chunk `i >> 4`: lookups cost `O(len/16 + 16)`); entries are evaluated
once (literal indices). -/
noncomputable def qTab (c : Ctx) (PT : Nat → Nat → TM) (sd : SumD) (b g lo hi : Nat) :
    List (List (Bool × TM)) :=
  mkList (fun j => mkList (fun l => L.qEnt c PT sd b (Nat.add (L.glo b g) (Nat.add (Nat.mul 16 j) l)) lo hi) 16)
    (Nat.add (Nat.shiftRight (Nat.sub (L.glo b (Nat.add g 1)) (L.glo b g)) 4) 1)

/-- Entry `i` of the `Q` table. -/
noncomputable def qAt (c : Ctx) (PT : Nat → Nat → TM) (sd : SumD) (b g lo hi i : Nat) : Bool × TM :=
  listAt (true, zeroTM) (listAt [] (L.qTab c PT sd b g lo hi) (Nat.shiftRight i 4)) (Nat.land i 15)

/-- Piece `(b, g, [lo,hi))` at one coordinate from its coefficient list `E = [(k, neg, m)]`, as one dot product
(classes without pairs in the owner range get the factor `zeroTM`). -/
noncomputable def pieceTM (c : Ctx) (PT : Nat → Nat → TM) (sd : SumD) (b g lo hi : Nat)
    (E : List (Nat × Bool × Nat)) : TM :=
  dotTM c (E.map fun e => (fun q => (cond q.1 zeroTM (constQ c e.2.1 e.2.2 (L.bden b)), q.2))
    (L.qAt c PT sd b g lo hi (Nat.sub e.1 (L.glo b g))))

end DegD

/-- Checkpoint slots of piece `(b, g, h)` at coordinate `r` (`n+1` coefficients, then the error). -/
def ckRecD (sd : SumD) (n b g h r : Nat) : List Nat :=
  decRec (sd.lay b) (Nat.add n 2) 0
    (recRaw (sd.chunk (Nat.add (Nat.mul 32 (Nat.add (Nat.mul 32 b) g)) h)) (sd.rw b) (sd.per b) r)

/-- Final sum slots at coordinate `r`. -/
def dRecD (sd : SumD) (n r : Nat) : List Nat :=
  decRec sd.dLay (Nat.add n 2) 0 (recRaw sd.dChunk sd.dRw sd.dPer r)

namespace DegD

variable (L : DegD)

/-- One piece at coordinate `r`: `ok` and the checkpoint `ck r`. -/
noncomputable def pieceOk (c : Ctx) (PT : Nat → Nat → TM) (sd : SumD) (b g lo hi : Nat)
    (ck : Nat → List Nat) (F n : Nat)
    (r : Nat) (E : List (Nat × Bool × Nat)) : Bool :=
  (fun T => T.ok && ckOk c F n T (ck r)) (L.pieceTM c PT sd b g lo hi E)

/-- Leaf checker: pieces `(b, g, h)`, `g0 ≤ g < g1`, at coordinates `r0 ≤ r < r1` are `ok` and match their
checkpoints (the coefficient lists `eTab (32 b + g)` are walked once). -/
noncomputable def leafOk (c : Ctx) (PT : Nat → Nat → TM) (sd : SumD) (n b g0 g1 h r0 r1 : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun g ih => cond (Nat.ble g0 g)
    (walkP (L.pieceOk c PT sd b g (sd.plo b h) (sd.plo b (Nat.add h 1)) (fun r => ckRecD sd n b g h r) sd.F n) r0 r1
      (L.eTab (Nat.add (Nat.mul 32 b) g)) 0 && ih) ih) g1

/-- The checkpoint records of all pieces at coordinate `r` (block-major). -/
def recsAtD (sd : SumD) (n r : Nat) : List (List Nat) :=
  (List.range (Nat.add L.dH 8)).flatMap fun b => (List.range (L.nGrp b)).flatMap fun g =>
    (List.range (sd.np b)).map fun h => ckRecD sd n b g h r

/-- The final record `D r` holds the coefficient sums and at least the error sum of the checkpoints. -/
def sumOkRD (sd : SumD) (n r : Nat) : Bool :=
  (fun a => smAll ((dRecD sd n r).take (Nat.add n 1)) a.1 && Nat.ble a.2 ((dRecD sd n r).getD (Nat.add n 1) 0))
    (accRecs (Nat.add n 1) (L.recsAtD sd n r) (List.replicate (Nat.add n 1) (0, 0), 0))

/-- Sum leaf: coordinates `r0 ≤ r < r1`. -/
def sumOkD (sd : SumD) (n r0 r1 : Nat) : Bool :=
  (List.range r1).all fun r => !(Nat.ble r0 r) || L.sumOkRD sd n r

/-- The owner parts of every block cover `[0, 512)` (`plo b 0 = 0`, monotone, `512 ≤ plo b (np b)`). -/
def partsOk (sd : SumD) : Bool :=
  (List.range (Nat.add L.dH 8)).all fun b => Nat.beq (sd.plo b 0) 0 && Nat.ble 512 (sd.plo b (sd.np b)) &&
    (List.range (sd.np b)).all fun h => Nat.ble (sd.plo b h) (sd.plo b (Nat.add h 1))

/-- Per-cell check: the inverse TMs of all shared denominators are valid (no denominator vanishes on the cell) and
the owner parts are a partition. -/
noncomputable def denOkD (c : Ctx) (A : TM) (sd : SumD) : Bool :=
  L.partsOk sd && (List.range L.nDen).all fun d => (invN c 8 0 (hornerQ c A (L.denQ d))).ok

end DegD

end ThomsonCompact.CoeffMap.Deg
