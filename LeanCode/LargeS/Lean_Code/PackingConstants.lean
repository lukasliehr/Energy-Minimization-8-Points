import Lean_Code.PackingGeometry

set_option maxHeartbeats 3000000

/-!
Exact constants and the explicit reference packing, independent of the
global packing theorem.
-/

open Real

noncomputable section

namespace SquareAntiprismVerification

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma aInf_quadratic : 7 * aInf ^ 2 + 2 * aInf - 1 = 0 := by
  have hs2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  unfold aInf
  nlinarith

/-- The final scalar implication in the paper's packing proof. -/
lemma scalar_packing_endgame {t : ℝ} (ht : 0 < t)
    (hpoly : 0 ≤ 7 * t ^ 2 + 2 * t - 1) : aInf ≤ t := by
  by_contra h
  have hta : t < aInf := lt_of_not_ge h
  have hmono : 7 * t ^ 2 + 2 * t < 7 * aInf ^ 2 + 2 * aInf := by
    nlinarith [aInf_mem_Ioo.1]
  nlinarith [aInf_quadratic]

lemma P_isConfiguration : IsConfiguration P := by
  unfold P
  exact X_isConfiguration aInf aInf_mem_Ioo

/-- Every squared distance of the limiting antiprism is at least its contact
distance `tau`.  This is a finite exact calculation over `ℚ(√2)`. -/
theorem P_pair_sq_ge_tau (i j : Fin 8) (hij : i ≠ j) :
    tau ≤ ‖P i - P j‖ ^ 2 := by
  unfold P
  rw [X_eq_Xc]
  have hs2 : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hra : √(1 - aInf) ^ 2 = 1 - aInf :=
    Real.sq_sqrt (by linarith [aInf_mem_Ioo.2])
  have hha : √aInf ^ 2 = aInf := Real.sq_sqrt (le_of_lt aInf_mem_Ioo.1)
  have hrs2 : (√(1 - aInf) * √2) ^ 2 = 2 * (1 - aInf) := by
    rw [mul_pow, hra, hs2]
    ring
  have hrel : 1 - aInf = 2 * √2 * aInf := by
    unfold aInf
    field_simp
    nlinarith [hs2]
  have hrasqrt : √(1 - aInf) ^ 2 * √2 = (1 - aInf) * √2 := by
    rw [hra]
  fin_cases i <;> fin_cases j <;>
    simp [Xc, norm_vec3_sub, r, h, tau] at hij ⊢ <;>
    (try rw [Real.sq_sqrt (by positivity)]) <;>
    nlinarith [hs2, hra, hha, hrs2, hrel, hrasqrt,
      sqrt_two_pos, sqrt_two_lt_two]

end SquareAntiprismVerification
