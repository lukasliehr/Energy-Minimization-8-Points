import AllS.Units.N_GI.N_tail_rational.N_analytic_bounds

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem trial_log_add_lower (x : ℝ) (hx : 0≤x) : x-x^2/2≤log (1+x) := by
  apply le_trans _ (Real.le_log_one_add_of_nonneg hx)
  apply (le_div_iff₀ (by linarith : 0<x+2)).mpr
  nlinarith [mul_nonneg hx (sq_nonneg x)]

theorem trial_log_sub_upper (x : ℝ) (hx : 0≤x) (hx1 : x<1) :
    -log (1-x)≤x+x^2/(2*(1-x)) := by
  let f : ℝ→ℝ := fun t=>t+t^2/(2*(1-t))+log (1-t)
  have hd (t : ℝ) (ht : t<1) :
      HasDerivAt f (t^2/(2*(1-t)^2)) t := by
    have hne : 1-t≠0 := by linarith
    have h := ((hasDerivAt_id t).add
      (((hasDerivAt_id t).pow 2).div
        (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).const_mul 2) (by positivity))).add
      (((hasDerivAt_const t 1).sub (hasDerivAt_id t)).log hne)
    convert! h using 1 <;> simp [f] <;> field_simp [hne] <;> ring
  have hm : MonotoneOn f (Set.Iio 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Iio 1)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (by simpa using ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t (by simpa using ht)).deriv]
      positivity
  have h := hm (by norm_num : (0:ℝ)∈Set.Iio 1) hx1 hx
  dsimp [f] at h
  norm_num at h
  linarith

theorem trial_exp_error (x : ℝ) (hx : 0≤x) (hx1 : x<1) :
    exp x≤1+x/(1-x) := by
  convert Real.exp_bound_div_one_sub_of_interval hx hx1 using 1
  have hne : 1-x≠0 := by linarith
  field_simp [hne]
  <;> ring

#print axioms trial_log_sub_upper
end Blueprint.Thomson.Tail.Implementation
