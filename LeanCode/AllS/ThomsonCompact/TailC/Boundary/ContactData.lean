import AllS.Units.N_AI.N_boundary_arithmetic.ContactAggregate
import ThomsonCompact.TailC.Boundary.Kernel

/-!
# TailC.Boundary: the contact data are the old exact contact quadratics (workstream TC1)

`contact_data`: for every contact `e = (i, d')`, the compact record list `gC (2 i + d')` (coefficients scaled by
`Dg = 17920000000`, sorted by quadratic index) converts to exactly the old normalized polynomial
`contactValue e`, whose evaluation is `boundaryContactPolynomial e` (`contactValue_eval`, proven in the old
project from the exact geometry, `GeometryKernels.contactRaw_eval`).
-/

namespace ThomsonCompact.TailC.Boundary
open ThomsonCompact.TailC Blueprint.CAP.BoundaryDirect

/-- `k mod 13` as a variable index. -/
def fin13 (k : Nat) : Fin 13 := ⟨k % 13, Nat.mod_lt _ (by decide)⟩

/-- The old word of the quadratic monomial `s` (`x_0 = 1`, `x_(j+1) = y_j`). -/
noncomputable def word (s : Nat) : Word :=
  bif Nat.beq (qb s) 0 then [] else
    bif Nat.beq (qa s) 0 then [fin13 (Nat.sub (qb s) 1)] else [fin13 (Nat.sub (qa s) 1), fin13 (Nat.sub (qb s) 1)]

/-- Sign-magnitude as a rational. -/
def smvQ (x : Bool × Nat) : ℚ := bif x.1 then -(x.2 : ℚ) else (x.2 : ℚ)

/-- The scale of the contact records. -/
def dG : Nat := 17920000000

/-- Record list → old sparse polynomial. -/
noncomputable def toPoly (l : List Ent) : Poly :=
  l.map (fun e => (word e.1, (smvQ e.2.1 / (dG : ℚ), smvQ e.2.2 / (dG : ℚ))))

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem contact_data : ∀ e : Blueprint.Thomson.Tail.ContactIndex,
    contactValue e = toPoly (decSV (gC (Nat.add (Nat.mul 2 e.1.val) e.2.val))) := by
  decide +kernel

end ThomsonCompact.TailC.Boundary
