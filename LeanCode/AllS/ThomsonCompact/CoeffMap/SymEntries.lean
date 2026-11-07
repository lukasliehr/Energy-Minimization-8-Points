/-!
# Symmetric sparse coefficient lists (Init only)

Shared by the per-cell programs (`Prog`) and the one-time table check (`ECheck`).
-/

namespace ThomsonCompact.CoeffMap

/-- Symmetric sparse coefficient list of a coefficient function `z` on `[0,n)²`: the pairs `u ≤ v` with
`c = z u u` (diagonal) or `c = z u v + z v u` (off-diagonal), `c ≠ 0`, as `(u, v, c < 0, |c|)`; column `v`
is appended at step `v + 1`. -/
def colEntries (z : Nat → Nat → Int) (v : Nat) : List (Nat × Nat × Bool × Nat) :=
  (List.range (v + 1)).filterMap fun u =>
    let c := if u = v then z v v else z u v + z v u
    if c = 0 then none else some (u, v, decide (c < 0), c.natAbs)

def symEntries (z : Nat → Nat → Int) : Nat → List (Nat × Nat × Bool × Nat)
  | 0 => []
  | n + 1 => symEntries z n ++ colEntries z n

end ThomsonCompact.CoeffMap
