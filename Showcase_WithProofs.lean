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

/-! ## Exact energies of the square antiprism -/

/-- The type of the pair `{i, j}` in `X(a)`: `0` on the diagonal, then `1`, `2`, `3`, `4` for the
squared distances `dA`, `dB`, `dC`, `dD`. -/
private def pairCode : Fin 8 → Fin 8 → Fin 5 :=
  ![![0, 1, 2, 1, 3, 4, 4, 3], ![1, 0, 1, 2, 3, 3, 4, 4], ![2, 1, 0, 1, 4, 3, 3, 4],
    ![1, 2, 1, 0, 4, 4, 3, 3], ![3, 3, 4, 4, 0, 1, 2, 1], ![4, 3, 3, 4, 1, 0, 1, 2],
    ![4, 4, 3, 3, 2, 1, 0, 1], ![3, 4, 4, 3, 1, 2, 1, 0]]

private theorem X_norm_sub {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) (i j : Fin 8) :
    ‖X a i - X a j‖ = √(![0, dA a, dB a, dC a, dD a] (pairCode i j)) := by
  have hr : √(1 - a) ^ 2 = 1 - a := Real.sq_sqrt (by linarith [ha.2])
  have hh : √a ^ 2 = a := Real.sq_sqrt ha.1.le
  have ht : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hti : (√(2 : ℝ))⁻¹ = √2 / 2 := by
    have h0 : √(2 : ℝ) ≠ 0 := by positivity
    field_simp
    linarith
  rw [← Real.sqrt_sq (norm_nonneg (X a i - X a j)), EuclideanSpace.real_norm_sq_eq]
  congr 1
  fin_cases i <;> fin_cases j
  all_goals simp [X, pairCode, dA, dB, dC, dD, Fin.sum_univ_succ, div_eq_mul_inv, hti]
  all_goals try ring_nf
  all_goals try simp only [hr, hh, ht]
  all_goals first | rfl | ring

private theorem dC_mul_dD (a : ℝ) : dC a * dD a = 2 * (1 + 6 * a + a ^ 2) := by
  have ht : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [dC, dD]
  linear_combination -(a - 1) ^ 2 * ht

private theorem dC_pos {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) : 0 < dC a := by
  have h2 : √(2 : ℝ) < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h0 : 0 ≤ √(2 : ℝ) := Real.sqrt_nonneg 2
  simp only [dC]
  nlinarith [ha.1]

private theorem dD_pos {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) : 0 < dD a := by
  have h2 : √(2 : ℝ) < 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h0 : 0 ≤ √(2 : ℝ) := Real.sqrt_nonneg 2
  simp only [dD]
  nlinarith [ha.1]

/-- The logarithmic energy of `X(a)`. -/
private theorem E_zero_X {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    E 0 (X a) = -12 * log 2 - 6 * log (1 - a) - 4 * log (1 + 6 * a + a ^ 2) := by
  have h1 : 0 < 1 - a := by linarith [ha.2]
  have hA : 0 < dA a := by simp only [dA]; linarith
  have hB : 0 < dB a := by simp only [dB]; linarith
  have hC := dC_pos ha
  have hD := dD_pos ha
  have hlA : log (dA a) = log 2 + log (1 - a) := by
    simp only [dA]; rw [Real.log_mul (by norm_num) h1.ne']
  have hlB : log (dB a) = 2 * log 2 + log (1 - a) := by
    simp only [dB]
    rw [Real.log_mul (by norm_num) h1.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hlCD : log (dC a) + log (dD a) = log 2 + log (1 + 6 * a + a ^ 2) := by
    rw [← Real.log_mul hC.ne' hD.ne', dC_mul_dD, Real.log_mul (by norm_num) (by nlinarith [ha.1])]
  simp only [E, if_true, X_norm_sub ha]
  simp [Finset.sum_filter, Fin.sum_univ_succ, pairCode, Real.log_sqrt, hA.le, hB.le, hC.le, hD.le]
  linarith

/-- The Coulomb energy of `X(a)`. -/
private theorem E_one_X {a : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    E 1 (X a) = (4 * √2 + 2) / √(1 - a) + 8 / √(dC a) + 8 / √(dD a) := by
  have h1 : 0 < 1 - a := by linarith [ha.2]
  have hsA : √(dA a) = √2 * √(1 - a) := by
    simp only [dA]; rw [Real.sqrt_mul (by norm_num)]
  have hsB : √(dB a) = 2 * √(1 - a) := by
    simp only [dB]
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have ht : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2 : 0 < √(2 : ℝ) := by positivity
  have hs1 : 0 < √(1 - a) := Real.sqrt_pos.2 h1
  simp only [E, one_ne_zero, if_false, X_norm_sub ha, Real.rpow_neg_one, div_one]
  simp [Finset.sum_filter, Fin.sum_univ_succ, pairCode, hsA, hsB]
  field_simp
  ring_nf
  simp only [ht]
  ring

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
  have hroot : ∀ s > (-2 : ℝ), a s ∈ Set.Ioo 0 1 ∧
      ∀ b ∈ Set.Ioo (0 : ℝ) 1, F s b = 0 ↔ b = a s := by
    intro s hs
    by_cases h : s < 0
    · rw [haNeg s h]
      exact hrootNeg' s ⟨hs, h⟩
    · rw [haPos s (not_lt.1 h)]
      exact hrootPos' s (not_lt.1 h)
  -- The closed forms of `E 0 (X a)` and `E 1 (X a)` hold for every `0 < a < 1`.
  refine ⟨a, hroot, by rw [haPos 0 le_rfl, ha₀], fun s hs => ?_,
    E_zero_X (hroot 0 (by norm_num)).1, E_one_X (hroot 1 (by norm_num)).1⟩
  by_cases h : s < 0
  · rw [haNeg s h]
    exact hminNeg' s ⟨hs, h⟩
  · rw [haPos s (not_lt.1 h)]
    exact hminPos' s (not_lt.1 h)

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
