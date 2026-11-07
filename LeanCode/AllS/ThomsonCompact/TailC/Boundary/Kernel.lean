import ThomsonCompact.TailC.Stage
import ThomsonCompact.TailC.Boundary.Tables
import ThomsonCompact.TailC.Boundary.Gam2
import ThomsonCompact.TailC.Boundary.DataF
import ThomsonCompact.TailC.Boundary.DataE

/-!
# TailC.Boundary: the boundary SOS check (kernel program, Init only; workstream TC1)

Level 1 (18 stages, `n = 14` affine monomials → `N = 105` quadratic monomials): the Grams `Σ_m λ_m ⊗ λ_m` of the
upper/lower/edge affine forms. Level 2 (one stage, `105 → 2380` quartic monomials): the 124 products
`D·1·1`, `cf H_k H_k`, `cu (4(1-N)) σ_u`, `cl (14884(N-ℓ)) σ_l`, `ce (Dg g_e) σ_e`, i.e. `-D·residual`.
`checkAll`: all stages pass their a-priori bounds and `Σ_γ max |q u_γ + p v_γ| < q D` for `p ∈ {pL, pU}`.
Parameters from `tools/tailc_boundary_export.py` (`params.json`).
-/

namespace ThomsonCompact.TailC.Boundary
open ThomsonCompact.TailC

/-! ## Parameters -/

def bD : Nat := 266721280000000000000000000000000000000000000
def cF : Nat := 66680320000000
def cU : Nat := 66680320000000
def cL : Nat := 17920000000
def cE : Nat := 3721
def sqQ : Nat := 1208925819614629174706176  -- 2^80
def sqL : Nat := 1709679290002018430137083
def sqU : Nat := 1709679290002018430137084

/-! ## Tables -/

/-- Quadratic monomial `s = x_(qa s) x_(qb s)`. -/
noncomputable def qa (s : Nat) : Nat := fld q2tab (Nat.mul 8 s) 4
noncomputable def qb (s : Nat) : Nat := fld q2tab (Nat.add (Nat.mul 8 s) 4) 4

/-- Level-1 table row `a` (14 entries of 8 bits). -/
noncomputable def g1row (a : Nat) : Nat := fld g1tab (Nat.mul 112 a) 112

/-- Quadratic index of `y_j²` (`x_(j+1)²`). -/
noncomputable def dIdx (j : Nat) : Nat := fld g1tab (Nat.mul 120 (Nat.add j 1)) 8

/-- `4 · qWeight j` as `(u, v)`. -/
def qw4 (j : Nat) : Nat × Nat :=
  bif Nat.beq j 9 || Nat.beq j 10 then (4, 2)
  else bif Nat.beq j 1 || Nat.beq j 2 || Nat.beq j 5 || Nat.beq j 6 || Nat.beq j 11 then (4, 1) else (8, 9)

/-! ## Stage parameters and terms -/

noncomputable def sp1 : SP := ⟨14, 105, 118, 127, 8, g1row⟩
noncomputable def sp2 : SP := ⟨105, 2380, 170, 185, 12, g2row⟩

/-- Gram terms of 14 affine forms. -/
noncomputable def gramTerms (src : Nat → Nat) : List Term := mkL (fun m => (decSV (src m), decSV (src m), 1)) 14

noncomputable def l1U : Bool × List Ent := stage sp1 (gramTerms lamU)
noncomputable def l1L : Bool × List Ent := stage sp1 (gramTerms lamL)
noncomputable def l1E (e : Nat) : Bool × List Ent := stage sp1 (gramTerms (fun m => lamE (Nat.add (Nat.mul 14 e) m)))

/-- `4 (1 - N)` and `14884 (N - ℓ)` (sorted by quadratic index). -/
noncomputable def nuL : List Ent :=
  (0, (false, 4), (false, 0)) :: mkL (fun j => (dIdx j, (true, (qw4 j).1), (true, (qw4 j).2))) 13
noncomputable def nlL : List Ent :=
  (0, (true, 14480), (false, 0)) ::
    mkL (fun j => (dIdx j, (false, Nat.mul 3721 (qw4 j).1), (false, Nat.mul 3721 (qw4 j).2))) 13

noncomputable def oneL : List Ent := [(0, (false, 1), (false, 0))]

/-- The Level-2 terms. -/
noncomputable def l2Terms : List Term :=
  (oneL, oneL, bD) :: (mkL (fun k => (decSV (hF k), decSV (hF k), cF)) 105 ++
    ((nuL, l1U.2, cU) :: (nlL, l1L.2, cL) :: mkL (fun e => (decSV (gC e), (l1E e).2, cE)) 16))

noncomputable def l2 : Bool × List Ent := stage sp2 l2Terms

/-! ## Final bound -/

/-- `|q u + p v|` for the entry value `u + v √2`. -/
noncomputable def linB (q p : Nat) (e : Ent) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.add (Nat.mul q e.2.1.2) (Nat.mul p e.2.2.2))
    (Nat.add (Nat.sub (Nat.mul q e.2.1.2) (Nat.mul p e.2.2.2)) (Nat.sub (Nat.mul p e.2.2.2) (Nat.mul q e.2.1.2)))
    (xor e.2.1.1 e.2.2.1)

noncomputable def maxN (a b : Nat) : Nat := Bool.rec (motive := fun _ => Nat) a b (Nat.ble a b)

noncomputable def bndSum (l : List Ent) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun e _ ih => Nat.add (maxN (linB sqQ sqL e) (linB sqQ sqU e)) ih) l

/-- All 16 Level-1 edge stages pass. -/
noncomputable def l1EOk : Bool := Nat.rec (motive := fun _ => Bool) true (fun e ih => ih && (l1E e).1) 16

/-- **The boundary check.** -/
noncomputable def checkAll : Bool :=
  l1U.1 && l1L.1 && l1EOk && l2.1 && Nat.blt (bndSum l2.2) (Nat.mul sqQ bD)

end ThomsonCompact.TailC.Boundary
