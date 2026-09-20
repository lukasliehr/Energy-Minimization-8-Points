import Thomson8.Interval
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

namespace Thomson8

noncomputable def logTaylor (n : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n+1), (-1 : ℝ)^(j+1) * z^j / j

theorem ofReal_logTaylor (n : ℕ) (z : ℝ) :
    (logTaylor n z : ℂ) = Complex.logTaylor (n+1) (z : ℂ) := by
  simp [logTaylor, Complex.logTaylor]

theorem log_taylor_bound (n : ℕ) {z : ℝ} (hz : |z| < 1) :
    |Real.log (1+z) - logTaylor n z| ≤ |z|^(n+1) * (1-|z|)⁻¹/(n+1) := by
  have hpos : 0 ≤ 1+z := by linarith [neg_abs_le z]
  have hc : ‖(z : ℂ)‖ < 1 := by simpa using hz
  have h := Complex.norm_log_sub_logTaylor_le n hc
  rw [← ofReal_logTaylor, ← Complex.ofReal_one, ← Complex.ofReal_add,
    ← Complex.ofReal_log hpos, ← Complex.ofReal_sub] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs, Nat.cast_add, Nat.cast_one] using h

theorem log_taylor_bound_uniform (n : ℕ) {z : ℝ} (hz : |z| ≤ 3/5) :
    |Real.log (1+z) - logTaylor n z| ≤ (3/5 : ℝ)^(n+1) * (1-3/5 : ℝ)⁻¹/(n+1) := by
  apply (log_taylor_bound n (lt_of_le_of_lt hz (by norm_num))).trans
  gcongr
  exact inv_nonneg.mpr (by linarith)

noncomputable def logApprox (n : ℕ) (z : ℝ) : ℝ := logTaylor n z - logTaylor n (-z)

theorem log_ratio_bound (n : ℕ) {z : ℝ} (hz : |z| ≤ 3/5) :
    |Real.log ((1+z)/(1-z)) - logApprox n z| ≤
      2*((3/5 : ℝ)^(n+1) * (1-3/5 : ℝ)⁻¹/(n+1)) := by
  have h₁ := log_taylor_bound_uniform n hz
  have h₂ := log_taylor_bound_uniform n (z := -z) (by simpa using hz)
  have hp : 0 < 1+z := by linarith [neg_abs_le z]
  have hm : 0 < 1-z := by linarith [le_abs_self z]
  rw [Real.log_div (ne_of_gt hp) (ne_of_gt hm)]
  unfold logApprox
  have hid : Real.log (1+z)-Real.log (1-z)-(logTaylor n z-logTaylor n (-z)) =
      (Real.log (1+z)-logTaylor n z)-(Real.log (1+(-z))-logTaylor n (-z)) := by
    simp only [sub_eq_add_neg]
    ring
  rw [hid]
  exact (abs_sub _ _).trans (by linarith)

theorem log_transformed_bound (n : ℕ) {x : ℝ} (hx : 0 < x)
    (hz : |(x-1)/(x+1)| ≤ 3/5) :
    |Real.log x - logApprox n ((x-1)/(x+1))| ≤
      2*((3/5 : ℝ)^(n+1) * (1-3/5 : ℝ)⁻¹/(n+1)) := by
  have heq : (1+(x-1)/(x+1))/(1-(x-1)/(x+1)) = x := by
    have hxp : x+1 ≠ 0 := by linarith
    field_simp
    <;> ring
  simpa only [heq] using log_ratio_bound n hz

end Thomson8
