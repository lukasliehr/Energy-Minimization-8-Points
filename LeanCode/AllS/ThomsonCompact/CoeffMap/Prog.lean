import ThomsonCompact.Packed.Core2
import ThomsonCompact.CoeffMap.SymEntries
import ThomsonCompact.CoeffMap.ListUtil

/-!
# Kernel programs of the coefficient-map mirror (Init only; imported by leaf modules)

Block contraction (soundness in `CoeffMap.Contract`): for a row-sparse column matrix (`row u` lists
`(i, entry)`, `none` is the exact constant `1`), Gram TMs `WT i j` and a sparse coefficient list `E` of
`(u, v, neg, m)` with denominator `den`,

  `zTM i v = Σ_{(j,e) ∈ row v} e · W i j`,  `pTM u v = Σ_{(i,e) ∈ row u} e · zTM i v`,
  `gTM = Σ_{(u,v,neg,m) ∈ E} (±m/den) · pTM u v`.
-/

namespace ThomsonCompact.CoeffMap

open ThomsonCompact.Packed

/-- Σ of a list of TMs (right fold, `zeroTM` for the empty list). -/
def sumTM (c : Ctx) : List TM → TM
  | [] => zeroTM
  | A :: L => add c A (sumTM c L)

/-- Multiplication by a column-matrix entry; `none` is the exact constant `1`. -/
def mulOpt (c : Ctx) : Option TM → TM → TM
  | none, A => A
  | some K, A => mul c K A

/-- Multiplication by the rational `±m / den`, rounded down to the scale (error one unit). -/
def smulQ (c : Ctx) (neg : Bool) (m den : Nat) (A : TM) : TM :=
  smul c neg (ratMag c m den) 1 A

/-- `Z i v = Σ_{(j,e) ∈ row v} e · W i j`. -/
def zTM (c : Ctx) (WT : Nat → Nat → TM) (row : Nat → List (Nat × Option TM)) (i v : Nat) : TM :=
  sumTM c ((row v).map fun p => mulOpt c p.2 (WT i p.1))

/-- `P u v = Σ_{(i,e) ∈ row u} e · Z i v = (K W Kᵀ)ᵤᵥ`. -/
def pTM (c : Ctx) (WT : Nat → Nat → TM) (row : Nat → List (Nat × Option TM)) (u v : Nat) : TM :=
  sumTM c ((row u).map fun p => mulOpt c p.2 (zTM c WT row p.1 v))

/-- `G = Σ_{(u,v,neg,m) ∈ E} (±m/den) · P u v`. -/
def gTM (c : Ctx) (WT : Nat → Nat → TM) (row : Nat → List (Nat × Option TM))
    (E : List (Nat × Nat × Bool × Nat)) (den : Nat) : TM :=
  sumTM c (E.map fun e => smulQ c e.2.2.1 e.2.2.2 den (pTM c WT row e.1 e.2.1))

/-- The table of all `pTM u v`, `u v < n` (built once; looked up by the coefficient lists, so that every
`pTM u v` is evaluated at most once by the kernel). -/
def pTab (c : Ctx) (WT : Nat → Nat → TM) (row : Nat → List (Nat × Option TM)) (n : Nat) : List (List TM) :=
  (List.range n).map fun u => (List.range n).map fun v => pTM c WT row u v

/-- `gTM` through the table `pTab` (equal to `gTM` when all entries index inside `[0,n)²`). -/
def gTMp (c : Ctx) (WT : Nat → Nat → TM) (row : Nat → List (Nat × Option TM)) (n : Nat)
    (E : List (Nat × Nat × Bool × Nat)) (den : Nat) : TM :=
  sumTM c (E.map fun e => smulQ c e.2.2.1 e.2.2.2 den (((pTab c WT row n).getD e.1 []).getD e.2.1 zeroTM))

end ThomsonCompact.CoeffMap

/-! ## Tabled contraction (F2c): every `zTM i v` and `pTM u v` is evaluated once -/

namespace ThomsonCompact.CoeffMap

open ThomsonCompact.Packed

/-- The table `zt[i][v] = zTM i v` (`i < n`, `v < m`). -/
noncomputable def zTab (c : Ctx) (WT : Nat → Nat → TM) (row : Nat → List (Nat × Option TM)) (n m : Nat) :
    List (List TM) :=
  mkList (fun i => mkList (fun v => zTM c WT row i v) m) n

/-- `zTM i v` through the table (direct computation outside `[0,n) × [0,m)`). -/
noncomputable def zLook (c : Ctx) (WT : Nat → Nat → TM) (row : Nat → List (Nat × Option TM))
    (zt : List (List TM)) (n m i v : Nat) : TM :=
  cond (Nat.blt i n && Nat.blt v m) (listAt zeroTM (listAt [] zt i) v) (zTM c WT row i v)

/-- Pivot column of a row consisting of a single exact `1`. -/
def pivotOf : List (Nat × Option TM) → Option Nat
  | [(j, none)] => some j
  | _ => none

/-- `(K W Kᵀ)ᵤᵥ` from the z table; for a pivot row `v = e_j`, by symmetry of `W`, `zTM j u`. -/
noncomputable def pTMz (c : Ctx) (WT : Nat → Nat → TM) (row : Nat → List (Nat × Option TM))
    (zt : List (List TM)) (n m u v : Nat) : TM :=
  Option.casesOn (motive := fun _ => TM) (pivotOf (row v))
    (sumTM c ((row u).map fun p => mulOpt c p.2 (zLook c WT row zt n m p.1 v)))
    (fun j => zLook c WT row zt n m j u)

/-- The table of all `pTMz u v`, `u v < k`. -/
noncomputable def pTabz (c : Ctx) (WT : Nat → Nat → TM) (row : Nat → List (Nat × Option TM))
    (zt : List (List TM)) (n m k : Nat) : List (List TM) :=
  mkList (fun u => mkList (fun v => pTMz c WT row zt n m u v) k) k

/-- `G = Σ_{(u,v,neg,m) ∈ E} (±m/den) · P u v` through the tables (`n` Gram columns, `m = k` raw rows). -/
noncomputable def gTMz (c : Ctx) (WT : Nat → Nat → TM) (row : Nat → List (Nat × Option TM)) (n m : Nat)
    (E : List (Nat × Nat × Bool × Nat)) (den : Nat) : TM :=
  sumTM c (E.map fun e => smulQ c e.2.2.1 e.2.2.2 den
    (listAt zeroTM (listAt [] (pTabz c WT row (zTab c WT row n m) n m m) e.1) e.2.1))

end ThomsonCompact.CoeffMap
