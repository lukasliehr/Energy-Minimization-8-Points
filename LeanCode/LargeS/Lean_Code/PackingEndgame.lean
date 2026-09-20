import Lean_Code.PackingConstants

open Real
noncomputable section
namespace SquareAntiprismVerification

lemma tan_half_sq_identity (β : ℝ) (hβ : β ∈ Set.Ioo (0 : ℝ) Real.pi) :
    Real.tan (β / 2) ^ 2 = (1 - Real.cos β) / (1 + Real.cos β) := by
  have hc : 0 < Real.cos (β / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hβ.1, Real.pi_pos], by linarith [hβ.2]⟩
  have htwo : Real.cos β = 2 * Real.cos (β / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (β / 2) using 1 <;> congr 1 <;> ring
  have hden : 0 < 1 + Real.cos β := by nlinarith [sq_pos_of_pos hc]
  rw [Real.tan_eq_sin_div_cos, div_pow]
  apply (div_eq_div_iff (pow_ne_zero _ hc.ne') hden.ne').mpr
  nlinarith [Real.sin_sq_add_cos_sq (β / 2)]

lemma packing_polynomial_identity (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    t * ((1 - (4 * (t / (1 + t)) ^ 3 - 3 * (t / (1 + t)))) /
      (1 + (4 * (t / (1 + t)) ^ 3 - 3 * (t / (1 + t))))) - 1 =
      (1 + t) * (7 * t ^ 2 + 2 * t - 1) / ((1 - t) ^ 2 * (1 + 2 * t)) := by
  have hplus : 1 + t ≠ 0 := by linarith [ht.1]
  have hminus : 1 - t ≠ 0 := by linarith [ht.2]
  have htwoplus : 1 + 2 * t ≠ 0 := by linarith [ht.1]
  have htwoplus' : 1 + t * 2 ≠ 0 := by linarith [ht.1]
  have hid : 1 + (4 * (t / (1 + t)) ^ 3 - 3 * (t / (1 + t))) =
      (1 - t) ^ 2 * (1 + 2 * t) / (1 + t) ^ 3 := by
    field_simp [hplus]
    ring
  rw [hid]
  field_simp [hplus, hminus, htwoplus, htwoplus']
  ring_nf

lemma packing_tan_polynomial_identity (t α β : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hcos : Real.cos α = t / (1 + t)) (hβeq : β = 2 * Real.pi - 3 * α)
    (hβ : β ∈ Set.Ioo (0 : ℝ) Real.pi) :
    t * Real.tan (β / 2) ^ 2 - 1 =
      (1 + t) * (7 * t ^ 2 + 2 * t - 1) / ((1 - t) ^ 2 * (1 + 2 * t)) := by
  rw [tan_half_sq_identity β hβ]
  have hcb : Real.cos β = 4 * (t / (1 + t)) ^ 3 - 3 * (t / (1 + t)) := by
    rw [hβeq, Real.cos_two_pi_sub, Real.cos_three_mul, hcos]
  rw [hcb]
  exact packing_polynomial_identity t ht

/-- The complete scalar endgame from the area inequality to the exact
quadratic packing bound. -/
theorem packing_bound_from_angles (t α β γ : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1)
    (hcos : Real.cos α = t / (1 + t)) (hβeq : β = 2 * Real.pi - 3 * α)
    (hβ : β ∈ Set.Ioo (0 : ℝ) Real.pi) (hγ : γ ∈ Set.Ioo (0 : ℝ) Real.pi)
    (hrhombus : Real.tan (β / 2) * Real.tan (γ / 2) = 1 / t)
    (harea : 6 * α + β + γ ≤ 4 * Real.pi) : aInf ≤ t := by
  have hγβ : γ ≤ β := by linarith
  have hβhalf : β / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hβ.1, Real.pi_pos], by linarith [hβ.2]⟩
  have hγhalf : γ / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hγ.1, Real.pi_pos], by linarith [hγ.2]⟩
  have htan : Real.tan (γ / 2) ≤ Real.tan (β / 2) :=
    Real.strictMonoOn_tan.monotoneOn hγhalf hβhalf (by linarith)
  have htanpos : 0 < Real.tan (β / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith [hβ.1]) (by linarith [hβ.2])
  have htineq : 1 ≤ t * Real.tan (β / 2) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left htan htanpos.le
    rw [hrhombus] at h
    have hm := mul_le_mul_of_nonneg_left h ht.1.le
    have hcancel : t * (1 / t) = 1 := by field_simp [ht.1.ne']
    rw [hcancel] at hm
    nlinarith
  have hid := packing_tan_polynomial_identity t α β ht hcos hβeq hβ
  have hden : 0 < (1 - t) ^ 2 * (1 + 2 * t) := by
    apply mul_pos (sq_pos_of_pos (by linarith [ht.2]))
    linarith [ht.1]
  have hquot : 0 ≤ (1 + t) * (7 * t ^ 2 + 2 * t - 1) /
      ((1 - t) ^ 2 * (1 + 2 * t)) := by linarith
  have hnum : 0 ≤ (1 + t) * (7 * t ^ 2 + 2 * t - 1) := by
    simpa using (le_div_iff₀ hden).mp hquot
  have hpoly : 0 ≤ 7 * t ^ 2 + 2 * t - 1 :=
    (mul_nonneg_iff_of_pos_left (by linarith [ht.1])).mp hnum
  exact scalar_packing_endgame ht.1 hpoly

theorem packing_angles_equality (α β γ : ℝ)
    (hcos : Real.cos α = aInf / (1 + aInf))
    (hβeq : β = 2 * Real.pi - 3 * α)
    (hβ : β ∈ Set.Ioo (0 : ℝ) Real.pi) (hγ : γ ∈ Set.Ioo (0 : ℝ) Real.pi)
    (hrhombus : Real.tan (β / 2) * Real.tan (γ / 2) = 1 / aInf) :
    γ = β ∧ 6 * α + β + γ = 4 * Real.pi := by
  have hid := packing_tan_polynomial_identity aInf α β aInf_mem_Ioo hcos hβeq hβ
  rw [aInf_quadratic, mul_zero, zero_div] at hid
  have htanpos : 0 < Real.tan (β / 2) :=
    Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith [hβ.1]) (by linarith [hβ.2])
  have hprod : Real.tan (β / 2) ^ 2 = 1 / aInf := by
    apply (eq_div_iff aInf_mem_Ioo.1.ne').mpr
    nlinarith
  have htaneq : Real.tan (γ / 2) = Real.tan (β / 2) := by
    apply mul_left_cancel₀ htanpos.ne'
    rw [hrhombus, ← hprod, pow_two]
  have heq : γ / 2 = β / 2 := Real.strictMonoOn_tan.injOn
    ⟨by linarith [hγ.1, Real.pi_pos], by linarith [hγ.2]⟩
    ⟨by linarith [hβ.1, Real.pi_pos], by linarith [hβ.2]⟩ htaneq
  constructor <;> linarith

end SquareAntiprismVerification
