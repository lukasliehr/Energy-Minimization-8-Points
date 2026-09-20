import Lean_Code.Parameter

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

def antiprismDistanceModel (a : ℝ) : Fin 8 → Fin 8 → ℝ :=
  ![![0, dA a, dB a, dA a, dC a, dD a, dD a, dC a],
    ![dA a, 0, dA a, dB a, dC a, dC a, dD a, dD a],
    ![dB a, dA a, 0, dA a, dD a, dC a, dC a, dD a],
    ![dA a, dB a, dA a, 0, dD a, dD a, dC a, dC a],
    ![dC a, dC a, dD a, dD a, 0, dA a, dB a, dA a],
    ![dD a, dC a, dC a, dD a, dA a, 0, dA a, dB a],
    ![dD a, dD a, dC a, dC a, dB a, dA a, 0, dA a],
    ![dC a, dD a, dD a, dC a, dA a, dB a, dA a, 0]]

set_option maxHeartbeats 3000000 in
lemma antiprism_sq_distance (a : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) 1) (i j : Fin 8) :
    ‖X a i - X a j‖ ^ 2 = antiprismDistanceModel a i j := by
  rw [X_eq_Xc]
  have hr : √(1 - a) ^ 2 = 1 - a := Real.sq_sqrt (by linarith [ha.2])
  have hh : √a ^ 2 = a := Real.sq_sqrt ha.1.le
  have hs : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  fin_cases i <;> fin_cases j <;>
    simp [Xc, norm_vec3_sub, r, h, antiprismDistanceModel, dA, dB, dC, dD] <;>
    (try rw [Real.sq_sqrt (by positivity)]) <;>
    ring_nf <;> (try simp only [hr, hh, hs]) <;> ring

def forceRadialCoefficient (s a : ℝ) : ℝ :=
  2 * dA a ^ (-q s) + dB a ^ (-q s) - 2 * dC a ^ (-q s) - 2 * dD a ^ (-q s)

set_option maxHeartbeats 3000000 in
/-- The finite symmetry calculation behind full stationarity: when `F=0`,
the weighted sum of the other vertices is radial at each of the eight points. -/
lemma antiprism_weighted_sum_radial (s a : ℝ) (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hF : F s a = 0) (i : Fin 8) :
    (∑ j : Fin 8 with j ≠ i, (‖X a i - X a j‖ ^ 2) ^ (-q s) • X a j) =
      forceRadialCoefficient s a • X a i := by
  simp_rw [antiprism_sq_distance a ha]
  have hbal : dA a ^ (-q s) = -dB a ^ (-q s) +
      (1 + √2 / 2) * dC a ^ (-q s) + (1 - √2 / 2) * dD a ^ (-q s) := by
    unfold F at hF
    linarith
  have hs : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [X_eq_Xc]
  fin_cases i <;> ext k <;> fin_cases k <;>
    simp [Finset.sum_filter, Fin.sum_univ_succ, antiprismDistanceModel, Xc,
      forceRadialCoefficient, hbal] <;>
    ring_nf <;> (try simp only [hs]) <;> ring

end SquareAntiprismVerification
