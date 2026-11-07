import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs

namespace Blueprint.CAP
open scoped BigOperators

def rationalBernsteinTransform (d i k : ℕ) : ℚ :=
  (∑ j ∈ Finset.Icc (k+i-d) (min i k),
    (-1:ℚ)^(k-j)*(i.choose j:ℚ)*((d-i).choose (k-j):ℚ)) / (d.choose k:ℚ)

def rationalRootControls {N : ℕ} (z : Fin (N+1) → ℤ) (i : Fin (N+1)) : ℚ :=
  ∑ k, rationalBernsteinTransform N i.val k.val * (z k:ℚ)/2^256

end Blueprint.CAP
