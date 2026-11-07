import LeanCode

/-!
# Energy minimization for eight points on the sphere

The two Lean-verified results of the paper: global optimality for every real
`s > -2`, with the exact minima for `s = 0` and `s = 1`, and a counterexample
for completely monotone potentials.
All definitions needed to read the statements are included here.
This companion supplies complete proofs of the statements in `Showcase.lean`.
-/

noncomputable section
open Real
open scoped BigOperators

namespace Thomson

/-! ## Configurations and energy -/

/-- Three-dimensional Euclidean space. -/
abbrev Point := EuclideanSpace ℝ (Fin 3)

/-- Eight distinct points on the unit sphere. -/
def IsConfiguration (Y : Fin 8 → Point) : Prop :=
  (∀ i, ‖Y i‖ = 1) ∧ Function.Injective Y

/-- The energy `E_s`, summed over the 28 unordered pairs; `s = 0` is logarithmic.
For `s ≠ 0` the sum is divided by `s`: for `s < 0`, minimizing `E_s` maximizes the sum of
distance powers, and for `s > 0` the division does not change the minimizers.
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

/-! ## Global optimality for every `s > -2` -/

/-- Global optimality for every real `s > -2`, with logarithmic energy at `s = 0`.
For each `s`, `a s` is the unique root of `F(s,·)` in `(0,1)` and `X(a s)` is the unique
minimizer up to congruence. The last two clauses give the exact minimal energies
for `s = 0` and `s = 1`. -/
theorem all_s_global_optimality :
    ∃ a : ℝ → ℝ,
      (∀ s > (-2 : ℝ), a s ∈ Set.Ioo 0 1 ∧
        ∀ b ∈ Set.Ioo (0 : ℝ) 1, F s b = 0 ↔ b = a s) ∧
      a 0 = (2 * √58 - 13) / 7 ∧
      (∀ s > (-2 : ℝ), IsUniqueMinimizer s (X (a s))) ∧
      E 0 (X (a 0)) = -12 * log 2 - 6 * log (1 - a 0)
        - 4 * log (1 + 6 * a 0 + a 0 ^ 2) ∧
      E 1 (X (a 1)) = (4 * √2 + 2) / √(1 - a 1)
        + 8 / √(dC (a 1)) + 8 / √(dD (a 1)) := by
  -- `LeanCode/AllS` proves the case `s ≥ 0`, stated with verbatim copies of the definitions above,
  -- except that its energy is not divided by `s`.
  obtain ⟨aPos, hrootPos, ha₀, hminPos⟩ := ThomsonCompact.Statement.all_s_global_optimality
  have hrootPos' : ∀ s ≥ (0 : ℝ), aPos s ∈ Set.Ioo 0 1 ∧
      ∀ b ∈ Set.Ioo (0 : ℝ) 1, F s b = 0 ↔ b = aPos s := hrootPos
  -- For `s > 0` the division by `s` does not change the minimizers.
  have hminPos' : ∀ s ≥ (0 : ℝ), IsUniqueMinimizer s (X (aPos s)) := by
    intro s hs
    obtain ⟨hZ, hmin⟩ := hminPos s hs
    refine ⟨hZ, fun Y hY => ?_⟩
    obtain ⟨hle, heq⟩ := hmin Y hY
    by_cases h₀ : s = 0
    · subst h₀
      have hE : ∀ Y, E 0 Y = ThomsonCompact.Statement.E 0 Y := by
        intro Y
        simp [E, ThomsonCompact.Statement.E]
      rw [hE, hE]
      exact ⟨hle, heq⟩
    · have hs : 0 < s := lt_of_le_of_ne hs (Ne.symm h₀)
      have hE : ∀ Y, E s Y = ThomsonCompact.Statement.E s Y / s := by
        intro Y
        simp only [E, ThomsonCompact.Statement.E, if_neg h₀, Finset.sum_div]
      rw [hE, hE, div_left_inj' h₀]
      exact ⟨div_le_div_of_nonneg_right hle hs.le, heq⟩
  -- `LeanCode/Negative_s` proves the case `-2 < s < 0`, stated with verbatim copies of the
  -- definitions above.
  obtain ⟨aNeg, hrootNeg, hminNeg⟩ := ThomsonNegative.Finalization.negative_s_global_optimality
  have hrootNeg' : ∀ s ∈ Set.Ioo (-2 : ℝ) 0, aNeg s ∈ Set.Ioo 0 1 ∧
      ∀ b ∈ Set.Ioo (0 : ℝ) 1, F s b = 0 ↔ b = aNeg s := hrootNeg
  have hminNeg' : ∀ s ∈ Set.Ioo (-2 : ℝ) 0, IsUniqueMinimizer s (X (aNeg s)) := hminNeg
  -- Join the two parameter functions at `s = 0`.
  obtain ⟨a, haNeg, haPos⟩ : ∃ a : ℝ → ℝ, (∀ s < 0, a s = aNeg s) ∧ ∀ s ≥ 0, a s = aPos s :=
    ⟨fun s => if s < 0 then aNeg s else aPos s, fun s hs => if_pos hs,
      fun s hs => if_neg (not_lt.2 hs)⟩
  -- At `s = 1` the stationary parameter is the Coulomb parameter.
  have hF₁ : F 1 Coulomb8.a = 0 := by
    change SquareAntiprismVerification.F 1 Coulomb8.a = 0
    rw [ThomsonCombined.stationarity_one Coulomb8.a ⟨Coulomb8.a_pos, Coulomb8.a_lt_one⟩,
      Coulomb8.F_a, mul_zero]
  have ha₁ : a 1 = Coulomb8.a :=
    (haPos 1 (by norm_num)).trans
      (((hrootPos' 1 (by norm_num)).2 Coulomb8.a ⟨Coulomb8.a_pos, Coulomb8.a_lt_one⟩).1 hF₁).symm
  refine ⟨a, fun s hs => ?_, by rw [haPos 0 le_rfl, ha₀], fun s hs => ?_, ?_, ?_⟩
  · by_cases h : s < 0
    · rw [haNeg s h]
      exact hrootNeg' s ⟨hs, h⟩
    · rw [haPos s (not_lt.1 h)]
      exact hrootPos' s (not_lt.1 h)
  · by_cases h : s < 0
    · rw [haNeg s h]
      exact hminNeg' s ⟨hs, h⟩
    · rw [haPos s (not_lt.1 h)]
      exact hminPos' s (not_lt.1 h)
  · -- Exact logarithmic minimum.
    rw [haPos 0 le_rfl, ha₀]
    have hX : X ((2 * √58 - 13) / 7) = Thomson8.antiprism := by
      simp only [X, Thomson8.antiprism, Thomson8.point, Thomson8.radius,
        Thomson8.height, Thomson8.a, neg_div]
    have hE : ∀ Y, E 0 Y = Thomson8.logEnergy Y := by
      intro Y
      simp [E, Thomson8.logEnergy]
    simpa only [hX, hE, Thomson8.optimalEnergy, Thomson8.a] using
      Thomson8.antiprism_energy
  · -- Exact Coulomb minimum.
    rw [ha₁]
    have hX : X Coulomb8.a = Coulomb8.antiprism := by
      simp only [X, Coulomb8.antiprism, Thomson8.point, Coulomb8.radius,
        Coulomb8.height, Coulomb8.q, neg_div]
    have hE : ∀ Y, E 1 Y = Coulomb8.coulombEnergy Y := by
      intro Y
      simp only [E, one_ne_zero, if_false, Real.rpow_neg_one, one_div, div_one,
        Coulomb8.coulombEnergy]
    simpa only [hX, hE, Coulomb8.optimalEnergy, Coulomb8.G,
      Coulomb8.q, Coulomb8.dMinus, Coulomb8.dPlus, dC, dD] using
      Coulomb8.antiprism_energy

/-! ## A counterexample for completely monotone potentials -/

namespace Monotonic

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

/-! ## Main theorem -/

/-- Counterexample to the square-antiprism assertion of Cohn and Woo's Conjecture 14.
One admissible configuration beats every square antiprism, including all
orthogonal images and relabelings. -/
theorem counterexample :
    0 < lambda ∧
    StrictlyCompletelyMonotone f ∧
    Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop ∧
    ∃ Y : Fin 8 → Point, IsConfiguration Y ∧
      ∀ a ∈ Set.Ioo (0 : ℝ) 1, ∀ Z : Fin 8 → Point,
        Congruent Z (X a) → Ef f Y < Ef f Z := by
  exact SquareAntiprismCounterexample.verified_counterexample

end Monotonic

end Thomson

#print axioms Thomson.all_s_global_optimality

#print axioms Thomson.Monotonic.counterexample
