import Mathlib

/-! Definitions copied from the local showcase; no proof placeholders. -/

noncomputable section
open Real
open scoped BigOperators

namespace ThomsonNegative

/-! ## Configurations and energy -/

/-- Three-dimensional Euclidean space. -/
abbrev Point := EuclideanSpace ℝ (Fin 3)

/-- Eight distinct points on the unit sphere. -/
def IsConfiguration (Y : Fin 8 → Point) : Prop :=
  (∀ i, ‖Y i‖ = 1) ∧ Function.Injective Y

/-- The normalized energy `E_s`, summed over the 28 unordered pairs; `s = 0` is logarithmic.
For `s < 0`, division by `s` is essential: minimizing this energy maximizes
the unnormalized sum of distance powers. Omitting the additive constant
`-28 / s` from the manuscript does not change the minimizers.
For real exponents, `d ^ t` denotes the real power `Real.rpow d t`. -/
def E (s : ℝ) (Y : Fin 8 → Point) : ℝ :=
  ∑ i : Fin 8, ∑ j : Fin 8 with i < j,
    if s = 0 then -log ‖Y i - Y j‖ else ‖Y i - Y j‖ ^ (-s) / s

/-- Congruence up to an orthogonal transformation and a permutation of the labels. -/
def Congruent (Y Z : Fin 8 → Point) : Prop :=
  ∃ (U : Point ≃ₗᵢ[ℝ] Point) (σ : Equiv.Perm (Fin 8)),
    ∀ i, Y i = U (Z (σ i))

/-- `Z` attains the global minimum, and equality occurs exactly at its congruent copies. -/
def IsUniqueMinimizer (s : ℝ) (Z : Fin 8 → Point) : Prop :=
  IsConfiguration Z ∧ ∀ Y, IsConfiguration Y →
    E s Z ≤ E s Y ∧ (E s Y = E s Z ↔ Congruent Y Z)

/-! ## The square antiprism and its optimal height -/

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

/-- The stationarity equation from the paper; `a` is the squared height. -/
def F (s a : ℝ) : ℝ :=
  let q := 1 + s / 2
  16 * dA a ^ (-q) + 16 * dB a ^ (-q)
    - 8 * (2 + √2) * dC a ^ (-q) - 8 * (2 - √2) * dD a ^ (-q)

end ThomsonNegative
