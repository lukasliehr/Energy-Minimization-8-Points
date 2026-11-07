import Mathlib

/-!
Positive coefficient recurrence for the rescaled auxiliary potential.
`seriesCoeff q n = (q+1)...(q+n)/(n+2)!`.
The separate identification with the Riesz potential is required before this
series can discharge an energy obligation.
-/

noncomputable section
open scoped BigOperators
namespace ThomsonNegative

def seriesCoeff (q : ℝ) : ℕ → ℝ
  | 0 => 1/2
  | n+1 => seriesCoeff q n * (q+n+1) / (n+3)

/-- Uniform coefficient bounds, including both removable endpoints. -/
theorem seriesCoeff_bounds (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) (n : ℕ) :
    0 < seriesCoeff q n ∧ seriesCoeff q n * (n+2) ≤ 1 := by
  induction n with
  | zero => norm_num [seriesCoeff]
  | succ n ih =>
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hp : (0 : ℝ) < n+3 := by positivity
    constructor
    · simp only [seriesCoeff]
      exact div_pos (mul_pos ih.1 (by linarith [hq.1])) hp
    · simp only [seriesCoeff, Nat.cast_add, Nat.cast_one]
      have he : (n : ℝ)+1+2 = n+3 := by ring
      rw [he, div_mul_cancel₀ _ (ne_of_gt hp)]
      nlinarith [hq.2]

/-- The coefficient sequence decreases; this also simplifies tail bounds. -/
theorem seriesCoeff_antitone (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    Antitone (seriesCoeff q) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [seriesCoeff]
  apply (div_le_iff₀ (show (0 : ℝ) < n+3 by positivity)).mpr
  apply mul_le_mul_of_nonneg_left _ (seriesCoeff_bounds q hq n).1.le
  linarith [hq.2]

/-- Each potential-series term is dominated by a geometric term. -/
theorem seriesTerm_bound (q x : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ seriesCoeff q n * x^(n+2) ∧
    seriesCoeff q n * x^(n+2) ≤ x^(n+2) / (n+2) := by
  have hn : (0 : ℝ) < n+2 := by positivity
  have hc : seriesCoeff q n ≤ 1/(n+2) :=
    (le_div_iff₀ hn).mpr (seriesCoeff_bounds q hq n).2
  refine ⟨mul_nonneg (seriesCoeff_bounds q hq n).1.le (pow_nonneg hx _), ?_⟩
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
    mul_le_mul_of_nonneg_right hc (pow_nonneg hx (n+2))

#print axioms seriesCoeff_bounds
#print axioms seriesCoeff_antitone
#print axioms seriesTerm_bound
end ThomsonNegative
