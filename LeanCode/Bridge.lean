import Mathlib
import LeanCode.MainTheorem

/-! The coordinates of the large-exponent development in the paper's notation. -/

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

end ThomsonCombined
