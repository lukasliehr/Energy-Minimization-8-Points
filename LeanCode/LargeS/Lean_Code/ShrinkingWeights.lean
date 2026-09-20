import Lean_Code.EnergyBounds

open Real
noncomputable section
namespace SquareAntiprismVerification

/-- Uniform lower bound for a contact's normalized positive Hessian weight. -/
lemma normalized_rpow_lower (B p x : ℝ) (hB : 0 ≤ B) (hp : 1 ≤ p)
    (hx : 0 < x) (hxupper : x ≤ 1 + B / p) :
    Real.exp (-3 * B) ≤ x ^ (-p - 2) := by
  have hppos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hlog : Real.log x ≤ B / p := by
    linarith [Real.log_le_sub_one_of_pos hx]
  have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ p + 2 by linarith)
  have hbp : B / p ≤ B := (div_le_iff₀ hppos).mpr (by nlinarith)
  have hcancel : p * (B / p) = B := by field_simp
  rw [Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Uniform upper bound for a normalized negative Hessian weight. -/
lemma normalized_rpow_upper (B p x : ℝ) (hB : 0 ≤ B) (hp : 1 ≤ p)
    (hpB : 2 * B ≤ p) (hxlower : 1 - B / p ≤ x) :
    x ^ (-p - 1) ≤ Real.exp (4 * B) := by
  have hppos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have ht : 0 ≤ B / p := div_nonneg hB hppos.le
  have ht_half : B / p ≤ 1 / 2 := (div_le_iff₀ hppos).mpr (by linarith)
  have hy : 0 < 1 - B / p := by linarith
  have hx : 0 < x := hy.trans_le hxlower
  have hinv : (1 - B / p)⁻¹ ≤ 1 + 2 * (B / p) := by
    rw [← one_div]
    apply (div_le_iff₀ hy).mpr
    nlinarith [mul_nonneg ht (show 0 ≤ 1 - 2 * (B / p) by linarith)]
  have hlogy := Real.one_sub_inv_le_log_of_pos hy
  have hlogx := Real.log_le_log hy hxlower
  have hlog : -2 * (B / p) ≤ Real.log x := by linarith
  have hmul := mul_le_mul_of_nonneg_left hlog (show 0 ≤ p + 1 by linarith)
  have hbp : B / p ≤ B := (div_le_iff₀ hppos).mpr (by nlinarith)
  have hcancel : p * (B / p) = B := by field_simp
  rw [Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  nlinarith

lemma shrinking_contact_weight_lower (τ B p d : ℝ) (hτ : 0 < τ)
    (hB : 0 ≤ B) (hp : 1 ≤ p) (hd : 0 < d)
    (hupper : d ≤ τ * (1 + B / p)) :
    τ ^ (-p - 2) * Real.exp (-3 * B) ≤ d ^ (-p - 2) := by
  have hx := normalized_rpow_lower B p (d / τ) hB hp (div_pos hd hτ)
    ((div_le_iff₀ hτ).mpr (by nlinarith))
  have h := mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hτ.le (-p - 2))
  have heq : τ * (d / τ) = d := by field_simp
  rw [← Real.mul_rpow hτ.le (div_nonneg hd.le hτ.le), heq] at h
  exact h

lemma shrinking_pair_weight_upper (τ B p d : ℝ) (hτ : 0 < τ)
    (hB : 0 ≤ B) (hp : 1 ≤ p) (hpB : 2 * B ≤ p)
    (hlower : τ * (1 - B / p) ≤ d) :
    d ^ (-p - 1) ≤ τ ^ (-p - 1) * Real.exp (4 * B) := by
  have hlow : 1 - B / p ≤ d / τ := (le_div_iff₀ hτ).mpr (by nlinarith)
  have hx := normalized_rpow_upper B p (d / τ) hB hp hpB hlow
  have hppos : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have ht_half : B / p ≤ 1 / 2 := (div_le_iff₀ hppos).mpr (by linarith)
  have hd : 0 ≤ d / τ := by linarith
  have h := mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hτ.le (-p - 1))
  have heq : τ * (d / τ) = d := by field_simp
  rw [← Real.mul_rpow hτ.le hd, heq] at h
  exact h

end SquareAntiprismVerification
