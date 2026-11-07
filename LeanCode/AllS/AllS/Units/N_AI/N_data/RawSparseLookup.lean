import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace Blueprint.CAP

def rawIntegerLookup (p : List ((ℕ × ℕ × ℕ) × ℤ)) (t : ℕ × ℕ × ℕ) : ℤ :=
  (p.map (fun e => if e.1=t then e.2 else 0)).sum

def rawRationalLookup (p : List ((ℕ × ℕ × ℕ) × ℚ)) (t : ℕ × ℕ × ℕ) : ℚ :=
  (p.map (fun e => if e.1=t then e.2 else 0)).sum

end Blueprint.CAP
