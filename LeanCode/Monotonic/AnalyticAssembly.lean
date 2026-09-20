import LeanCode.Monotonic.Family
import LeanCode.Monotonic.Estimates
import LeanCode.Monotonic.AssemblyAlgebra
import LeanCode.Monotonic.Calculus

noncomputable section
open Real Set
namespace SquareAntiprismCounterexample

lemma fast_slope_pos : 0 < L aStar h1 := by
  have hp : 0 < 8*(n:ℝ)/dStar := div_pos (mul_pos (by norm_num) n_pos) dStar_pos
  exact lt_trans hp fast_bounds.1

lemma slow_slope_neg : L aStar g1 < 0 := by
  have hs := slow_bounds.2.1
  have hp : 0 ≤ (n:ℝ)^3 := (pow_pos n_pos 3).le
  by_contra hnot
  have hn := mul_nonneg hp (le_of_not_gt hnot)
  linarith

lemma lambda_pos : 0 < lambda :=
  coefficient_positive slow_slope_neg fast_slope_pos lambda_eq

lemma family_minimum : ∀ a ∈ Ioo (0:ℝ) 1, G f aStar ≤ G f a := by
  exact stationary_minimum aStar_mem
    (fun a ha => family_hasDerivAt f f1 (fun _ ht => f_hasDerivAt ht) ha)
    (fun a ha => familySlope_hasDerivAt f1 f2 (fun _ ht => f1_hasDerivAt ht) ha)
    (fun a ha => familySecond_pos f2 (fun _ ht => f2_pos lambda_pos ht) ha)
    (mixture_stationary fast_slope_pos.ne' lambda_eq)

lemma negative_variation : Q aStar f1 f2 < 0 :=
  mixture_variation_negative slow_bounds.1 slow_bounds.2.1 slow_bounds.2.2
    fast_slope_pos fast_bounds.2 lambda_eq

end SquareAntiprismCounterexample
