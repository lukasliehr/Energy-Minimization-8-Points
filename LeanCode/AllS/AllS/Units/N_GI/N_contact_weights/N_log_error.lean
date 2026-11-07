import AllS.Units.N_GI.N_contact_weights.N_hessian_weight

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem log_one_add_quadratic_error (y : ℝ) (hy : |y|<1) :
    |log (1+y)-y|≤y^2/(2*(1-|y|)) := by
  have ha := abs_lt.mp hy
  have hden : 0<2*(1-|y|) := by linarith
  have hlog := Real.log_le_sub_one_of_pos (show 0<1+y by linarith)
  rw [abs_of_nonpos (by linarith : log (1+y)-y≤0)]
  by_cases hy0 : 0≤y
  · have hl := trial_log_add_lower y hy0
    have hb : y^2/2≤y^2/(2*(1-|y|)) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith [mul_nonneg (sq_nonneg y) (abs_nonneg y)]
    linarith
  · have hyn : y≤0 := le_of_not_ge hy0
    have hl := trial_log_sub_upper (-y) (by linarith) (by linarith)
    rw [abs_of_nonpos hyn]
    simp only [sub_neg_eq_add,neg_sq] at hl ⊢
    linarith

theorem scaled_log_quadratic_error (p y : ℝ) (hp : (97:ℝ)/2≤p) (hy : |p*y|<3) :
    |p*(log (1+y)-y)|≤9/(2*(p-3)) := by
  have hp0 : 0<p := by linarith
  rw [abs_mul,abs_of_pos hp0] at hy ⊢
  have hb : |y|<3/p := (lt_div_iff₀ hp0).mpr (by nlinarith [hy])
  have hquot : 3/p<1 := (div_lt_one hp0).mpr (by linarith)
  have hy1 : |y|<1 := hb.trans hquot
  have hs : y^2≤(3/p)^2 := by
    have h := mul_nonneg (sub_nonneg.mpr hb.le) (by positivity : 0≤3/p+|y|)
    nlinarith [sq_abs y]
  have hL := mul_le_mul_of_nonneg_left (log_one_add_quadratic_error y hy1) hp0.le
  calc
    _ ≤ p*(y^2/(2*(1-|y|))) := hL
    _ = (p*y^2)/(2*(1-|y|)) := by ring
    _ ≤ (p*y^2)/(2*(1-3/p)) :=
      div_le_div_of_nonneg_left (by positivity) (by linarith) (by linarith)
    _ ≤ (p*(3/p)^2)/(2*(1-3/p)) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hp0.le) (by linarith)
    _ = _ := by field_simp <;> ring

theorem contact_weights_log_error (p : ℝ) (hp : (97:ℝ)/2≤p) (q : TangentCoordinates)
    (hq : q∈convexTailDomain p) (e : ContactIndex) :
    |p*log (squaredDistance (orthographicChart q) e.1 (contactNext e)/tau)-contactScaledLinear p q e|<3/25 := by
  let y : ℝ := contactDelta q e.1 (contactNext e)/tau
  have he : (p/tau)*contactDelta q e.1 (contactNext e)=p*y := by dsimp [y]; ring
  have hy := (contact_weights_linear_lower p hp q hq e).2
  rw [he] at hy
  have ht := contact_scaled_taylor_error p hp q hq.2.1 e
  rw [he] at ht
  have hl := scaled_log_quadratic_error p y hp hy
  have hid : squaredDistance (orthographicChart q) e.1 (contactNext e)/tau=1+y := by
    dsimp [y,contactDelta]
    field_simp [tau_pos.ne']
    <;> ring
  rw [hid]
  have hsplit : p*log (1+y)-contactScaledLinear p q e=
      p*(log (1+y)-y)+(p*y-contactScaledLinear p q e) := by ring
  rw [hsplit]
  have htri := (abs_add_le _ _).trans (add_le_add hl ht)
  have hquot : 9/(2*(p-3))≤9/(2*((97:ℝ)/2-3)) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hε := (tail_epsilon_bounds p hp).2
  norm_num at hquot
  linarith

#print axioms contact_weights_log_error
end Blueprint.Thomson.Tail.Implementation
