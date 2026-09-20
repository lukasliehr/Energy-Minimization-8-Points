import Mathlib

/-!
# Definitions for the completely monotone counterexample

These definitions agree with the paper's public definitions in `Showcase.lean`.
The proof library uses its own namespace, as do the other three developments,
so both showcases can retain their self-contained mathematical statements.
`Showcase_WithProofs.lean` transfers the result by definitional equality.
-/

noncomputable section
open Real
open scoped BigOperators

namespace SquareAntiprismCounterexample

/-! ## Definitions shared with the preceding paper -/

/-- Three-dimensional Euclidean space. -/
abbrev Point := EuclideanSpace ℝ (Fin 3)

/-- Eight distinct points on the unit sphere. -/
def IsConfiguration (Y : Fin 8 → Point) : Prop :=
  (∀ i, ‖Y i‖ = 1) ∧ Function.Injective Y

/-- Congruence up to an orthogonal transformation and a permutation of the labels. -/
def Congruent (Y Z : Fin 8 → Point) : Prop :=
  ∃ (U : Point ≃ₗᵢ[ℝ] Point) (σ : Equiv.Perm (Fin 8)),
    ∀ i, Y i = U (Z (σ i))

/-- `X(a)` consists of two squares at heights `±√a`, with relative rotation `π/4`.
Here `!₂[x, y, z]` is the Euclidean vector with coordinates `(x,y,z)`. -/
def X (a : ℝ) : Fin 8 → Point :=
  let r := √(1 - a)
  let h := √a
  let d := r / √2
  ![!₂[r, 0, h], !₂[0, r, h], !₂[-r, 0, h], !₂[0, -r, h],
    !₂[d, d, -h], !₂[-d, d, -h], !₂[-d, -d, -h], !₂[d, -d, -h]]

/-- The four squared distances in `X(a)`. -/
def dA (a : ℝ) : ℝ := 2 * (1 - a)
def dB (a : ℝ) : ℝ := 4 * (1 - a)
def dC (a : ℝ) : ℝ := 2 - √2 + (2 + √2) * a
def dD (a : ℝ) : ℝ := 2 + √2 + (2 - √2) * a


open scoped ContDiff

/-! ## Potentials of squared distance -/

/-- The potential is applied to squared Euclidean distance. -/
def Ef (v : ℝ → ℝ) (Y : Fin 8 → Point) : ℝ :=
  ∑ i : Fin 8, ∑ j : Fin 8 with i < j,
    v (‖Y i - Y j‖ ^ 2)

/-- Smoothness and strict sign alternation of every derivative on `(0,∞)`.
The order `k = 0` includes strict positivity of the potential itself. -/
def StrictlyCompletelyMonotone (v : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ v (Set.Ioi 0) ∧
    ∀ k : ℕ, ∀ r : ℝ, 0 < r →
      0 < (-1 : ℝ) ^ k * iteratedDeriv k v r

/-- The energy of the antiprism family, expressed using its distance multiplicities. -/
def G (v : ℝ → ℝ) (a : ℝ) : ℝ :=
  8 * v (dA a) + 4 * v (dB a) + 8 * v (dC a) + 8 * v (dD a)

/-! ## The explicit potential -/

def aStar : ℝ := 5 / 18
def n : ℕ := 10000
def dStar : ℝ := 13 / 9

def g (r : ℝ) : ℝ := 1 / ((n : ℝ) + r)
def h (r : ℝ) : ℝ := (dStar / r) ^ n

/-- The constants in `g` and `h` are held fixed when differentiating in `a`. -/
def lambda : ℝ := -(deriv (G g) aStar) / deriv (G h) aStar

def f (r : ℝ) : ℝ := g r + lambda * h r

end SquareAntiprismCounterexample
