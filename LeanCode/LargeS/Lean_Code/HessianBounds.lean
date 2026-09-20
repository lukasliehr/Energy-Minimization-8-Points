import Lean_Code.EnergyHessian

open Real
noncomputable section
namespace SquareAntiprismVerification

lemma finite_hessian_lower_bound {ι : Type} [DecidableEq ι]
    (s : Finset ι) (d g h : ι → ℝ) (p A C M c n : ℝ)
    (hp : 0 ≤ p) (hA : 0 ≤ A) (hC : 0 ≤ C) (hc : 0 ≤ c) (hn : 0 ≤ n)
    (hd : ∀ i ∈ s, 0 ≤ d i)
    (hweight : ∀ i ∈ s, d i ^ (-p - 1) ≤ C)
    (hsecond : ∀ i ∈ s, |h i| ≤ M * n ^ 2)
    (e : ι) (he : e ∈ s) (heweight : A ≤ d e ^ (-p - 2))
    (herank : c * n ≤ |g e|) :
    p * ((p + 1) * A * c ^ 2 - s.card * C * M) * n ^ 2 ≤
      p * (p + 1) * (∑ i ∈ s, d i ^ (-p - 2) * (g i) ^ 2) -
      p * (∑ i ∈ s, d i ^ (-p - 1) * h i) := by
  have hsq : c ^ 2 * n ^ 2 ≤ (g e) ^ 2 := by
    have hh := mul_nonneg (sub_nonneg.mpr herank)
      (add_nonneg (abs_nonneg (g e)) (mul_nonneg hc hn))
    nlinarith [sq_abs (g e)]
  have hterm : A * (c ^ 2 * n ^ 2) ≤ d e ^ (-p - 2) * (g e) ^ 2 := by
    exact mul_le_mul heweight hsq (mul_nonneg (sq_nonneg c) (sq_nonneg n))
      (Real.rpow_nonneg (hd e he) _)
  have hsingle : d e ^ (-p - 2) * (g e) ^ 2 ≤
      ∑ i ∈ s, d i ^ (-p - 2) * (g i) ^ 2 :=
    Finset.single_le_sum (fun i hi => mul_nonneg (Real.rpow_nonneg (hd i hi) _)
      (sq_nonneg _)) he
  have hpositive := mul_le_mul_of_nonneg_left (hterm.trans hsingle)
    (mul_nonneg hp (show 0 ≤ p + 1 by linarith))
  have hnegative : (∑ i ∈ s, d i ^ (-p - 1) * h i) ≤
      s.card * (C * (M * n ^ 2)) := by
    calc
      (∑ i ∈ s, d i ^ (-p - 1) * h i) ≤ ∑ _i ∈ s, C * (M * n ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        have hh := mul_le_mul_of_nonneg_left (le_abs_self (h i))
          (Real.rpow_nonneg (hd i hi) (-p - 1))
        exact hh.trans (mul_le_mul (hweight i hi) (hsecond i hi) (abs_nonneg _) hC)
      _ = s.card * (C * (M * n ^ 2)) := by simp
  have hnscaled := mul_le_mul_of_nonneg_left hnegative hp
  nlinarith

lemma hessian_bracket_eventually_positive (a D : ℝ) (ha : 0 < a) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p ≥ p₀, 0 < (p + 1) * a - D := by
  refine ⟨max 1 (D / a), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro p hp
  have hpa : D / a ≤ p := (le_max_right _ _).trans hp
  have hd := (div_le_iff₀ ha).mp hpa
  nlinarith

end SquareAntiprismVerification
