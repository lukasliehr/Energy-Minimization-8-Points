import Mathlib
import LeanCode.MainTheorem

/-! Coordinate and stationarity conversions between the three developments. -/

noncomputable section
open Real
open scoped BigOperators

namespace ThomsonCombined

theorem antiprism_coordinates (a : ℝ) :
    SquareAntiprismVerification.X a =
      let r := √(1 - a)
      let h := √a
      let d := r / √2
      ![!₂[r, 0, h], !₂[0, r, h], !₂[-r, 0, h], !₂[0, -r, h],
        !₂[d, d, -h], !₂[-d, d, -h], !₂[-d, -d, -h], !₂[d, -d, -h]] := by
  have htwo : (2 : ℝ) * π / 2 = π := by ring
  have hthree : (3 : ℝ) * π / 2 = π + π / 2 := by ring
  have hsqrt : (√(2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt_ne : √(2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hdiv : ∀ r : ℝ, r * (√2 / 2) = r / √2 := by
    intro r
    field_simp
    linear_combination r * hsqrt
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SquareAntiprismVerification.X, SquareAntiprismVerification.r,
      SquareAntiprismVerification.h, Fin.append, Fin.addCases, htwo, hthree,
      Real.cos_add, Real.sin_add, hdiv, mul_neg]

private theorem rpow_neg_three_halves {x : ℝ} (hx : 0 < x) :
    x ^ (-(1 + (1 : ℝ) / 2)) = 1 / (x * √x) := by
  rw [Real.rpow_neg hx.le, Real.rpow_add hx, Real.rpow_one,
    ← Real.sqrt_eq_rpow, one_div]

/-- The paper's `F(1,a)` is twice the Coulomb development's stationarity function. -/
theorem stationarity_one (a : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) 1) :
    SquareAntiprismVerification.F 1 a = 2 * Coulomb8.F a := by
  have ht : 0 < 1 - a := sub_pos.2 ha.2
  have hA : 0 < SquareAntiprismVerification.dA a := by
    dsimp [SquareAntiprismVerification.dA]; positivity
  have hB : 0 < SquareAntiprismVerification.dB a := by
    dsimp [SquareAntiprismVerification.dB]; positivity
  have hC : 0 < SquareAntiprismVerification.dC a := Coulomb8.dMinus_pos ha.1
  have hD : 0 < SquareAntiprismVerification.dD a := Coulomb8.dPlus_pos ha.1
  have hs2 : (√(2 : ℝ)) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn2 : √(2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hi2 : (√(2 : ℝ))⁻¹ = √2 / 2 := by
    field_simp
    nlinarith [hs2]
  simp only [SquareAntiprismVerification.F, SquareAntiprismVerification.q,
    rpow_neg_three_halves hA, rpow_neg_three_halves hB,
    rpow_neg_three_halves hC, rpow_neg_three_halves hD]
  dsimp [SquareAntiprismVerification.dA, SquareAntiprismVerification.dB,
    SquareAntiprismVerification.dC, SquareAntiprismVerification.dD,
    Coulomb8.F, Coulomb8.dMinus, Coulomb8.dPlus, Coulomb8.q]
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  rw [show Real.sqrt 4 = 2 by norm_num]
  simp only [div_eq_mul_inv, mul_inv_rev, hi2]
  ring

end ThomsonCombined
