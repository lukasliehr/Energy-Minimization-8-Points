import LeanCode

/-!
# Energy minimization for eight points on the sphere

The four Lean-verified results of the paper: `s = 0`, `s = 1`, all sufficiently
large `s`, and a counterexample for completely monotone potentials.
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
For real exponents, `d ^ t` denotes the real power `Real.rpow d t`. -/
def E (s : ℝ) (Y : Fin 8 → Point) : ℝ :=
  ∑ i : Fin 8, ∑ j : Fin 8 with i < j,
    if s = 0 then -log ‖Y i - Y j‖ else ‖Y i - Y j‖ ^ (-s)

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

/-! ## Logarithmic energy (`s = 0`): exact minimum and uniqueness -/

/-- The logarithmic case of Global optimality and Exact logarithmic minimum. -/
theorem logarithmic_minimum :
    let a₀ := (2 * √58 - 13) / 7
    IsUniqueMinimizer 0 (X a₀) ∧
      E 0 (X a₀) = -12 * log 2 - 6 * log (1 - a₀)
        - 4 * log (1 + 6 * a₀ + a₀ ^ 2) := by
  dsimp only
  have hX : X ((2 * √58 - 13) / 7) = Thomson8.antiprism := by
    simp only [X, Thomson8.antiprism, Thomson8.point, Thomson8.radius,
      Thomson8.height, Thomson8.a, neg_div]
  have hE : ∀ Y, E 0 Y = Thomson8.logEnergy Y := by
    intro Y
    simp [E, Thomson8.logEnergy]
  constructor
  · refine ⟨?_, ?_⟩
    · simpa only [hX, IsConfiguration, Thomson8.Admissible] using
        Thomson8.antiprism_admissible
    · intro Y hY
      simpa only [hX, hE, Thomson8.antiprism_energy, Congruent, Thomson8.Congruent] using
        Thomson8.logarithmic_energy_N8_global_minimizer Y hY
  · simpa only [hX, hE, Thomson8.optimalEnergy, Thomson8.a] using
      Thomson8.antiprism_energy

/-! ## Coulomb energy (`s = 1`): Thomson's problem for eight points -/

/-- The Coulomb case of Global optimality and Exact Coulomb minimum.
The first two clauses characterize `a₁` as the unique root of `F(1,·)` in `(0,1)`. -/
theorem coulomb_minimum :
    ∃ a₁ ∈ Set.Ioo (0 : ℝ) 1,
      (∀ b ∈ Set.Ioo (0 : ℝ) 1, F 1 b = 0 ↔ b = a₁) ∧
      IsUniqueMinimizer 1 (X a₁) ∧
      E 1 (X a₁) = (4 * √2 + 2) / √(1 - a₁)
        + 8 / √(dC a₁) + 8 / √(dD a₁) := by
  refine ⟨Coulomb8.a, ⟨Coulomb8.a_pos, Coulomb8.a_lt_one⟩, ?_, ?_, ?_⟩
  · intro b hb
    change SquareAntiprismVerification.F 1 b = 0 ↔ b = Coulomb8.a
    rw [ThomsonCombined.stationarity_one b hb]
    constructor
    · intro h
      exact Coulomb8.root_unique hb (by linarith)
    · rintro rfl
      rw [Coulomb8.F_a, mul_zero]
  all_goals
    have hX : X Coulomb8.a = Coulomb8.antiprism := by
      simp only [X, Coulomb8.antiprism, Thomson8.point, Coulomb8.radius,
        Coulomb8.height, Coulomb8.q, neg_div]
    have hE : ∀ Y, E 1 Y = Coulomb8.coulombEnergy Y := by
      intro Y
      simp only [E, one_ne_zero, if_false, Real.rpow_neg_one, one_div,
        Coulomb8.coulombEnergy]
  · refine ⟨?_, ?_⟩
    · simpa only [hX, IsConfiguration, Coulomb8.Admissible, Thomson8.Admissible] using
        Coulomb8.antiprism_admissible
    · intro Y hY
      simpa only [hX, hE, Congruent] using
        Coulomb8.coulomb_energy_N8_solution Y hY.1 hY.2
  · simpa only [hX, hE, Coulomb8.optimalEnergy, Coulomb8.G,
      Coulomb8.q, Coulomb8.dMinus, Coulomb8.dPlus, dC, dD] using
      Coulomb8.antiprism_energy

/-! ## Riesz energy for all sufficiently large `s` -/

/-- The eventual case of Global optimality, including the unique parameter for every `s ≥ 0`.
The threshold `S > 0` is existential; no numerical upper bound is asserted. -/
theorem eventual_global_optimality :
    ∃ a : ℝ → ℝ,
      (∀ s ≥ (0 : ℝ), a s ∈ Set.Ioo 0 1 ∧
        ∀ b ∈ Set.Ioo (0 : ℝ) 1, F s b = 0 ↔ b = a s) ∧
      a 0 = (2 * √58 - 13) / 7 ∧
      ∃ S > 0, ∀ s ≥ S, IsUniqueMinimizer s (X (a s)) := by
  obtain ⟨a, hroot, ha₀, S, hS, htail⟩ :=
    SquareAntiprismVerification.eventual_global_optimality
  refine ⟨a, ?_, ha₀, S, by linarith, ?_⟩
  · intro s hs
    obtain ⟨ha, hF, hu⟩ := hroot s hs
    refine ⟨ha, fun b hb => ⟨hu b hb, ?_⟩⟩
    rintro rfl
    exact hF
  · intro s hs
    have hspos : 0 < s := by linarith
    have hX : X (a s) = SquareAntiprismVerification.X (a s) :=
      (ThomsonCombined.antiprism_coordinates (a s)).symm
    have hE : ∀ Y, E s Y = SquareAntiprismVerification.E s Y := by
      intro Y
      simp only [E, if_neg hspos.ne', SquareAntiprismVerification.E]
    refine ⟨?_, ?_⟩
    · simpa only [hX, IsConfiguration, SquareAntiprismVerification.IsConfiguration,
        SquareAntiprismVerification.unitSphere, Set.mem_ofPred_eq] using
        SquareAntiprismVerification.X_isConfiguration (a s) (hroot s hspos.le).1
    · intro Y hY
      obtain ⟨hbound, heq⟩ := (htail s hs).1 Y hY
      refine ⟨?_, ?_⟩
      · simpa only [hX, hE] using hbound
      · rw [hE, hE, hX]
        exact heq.trans ⟨SquareAntiprismVerification.congruent_symm,
          SquareAntiprismVerification.congruent_symm⟩

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

#print axioms Thomson.logarithmic_minimum
#print axioms Thomson.coulomb_minimum
#print axioms Thomson.eventual_global_optimality

#print axioms Thomson.Monotonic.counterexample
