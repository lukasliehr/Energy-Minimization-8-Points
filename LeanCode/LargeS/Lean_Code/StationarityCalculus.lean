import Lean_Code.EnergyHessian

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma energy_sq_pair_sum (p : ℝ) (Y : Fin 8 → ℝ³) :
    E (2 * p) Y = ∑ ij ∈ energyPairs, (‖Y ij.1 - Y ij.2‖ ^ 2) ^ (-p) := by
  simp only [E, energyPairs, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs
  · exact norm_rpow_two_mul _ p
  · rfl

theorem energy_curve_hasDerivAt (p : ℝ) (Y V : Fin 8 → ℝ³)
    (γ : ℝ → Fin 8 → ℝ³) (hY : IsConfiguration Y) (hγzero : γ 0 = Y)
    (hγ : ∀ i, HasDerivAt (fun t => γ t i) (V i) 0) :
    HasDerivAt (fun t => E (2 * p) (γ t))
      (-2 * p * ∑ ij ∈ energyPairs,
        (‖Y ij.1 - Y ij.2‖ ^ 2) ^ (-p - 1) *
          inner ℝ (Y ij.1 - Y ij.2) (V ij.1 - V ij.2)) 0 := by
  have hterm : ∀ ij ∈ energyPairs,
      HasDerivAt (fun t => (‖γ t ij.1 - γ t ij.2‖ ^ 2) ^ (-p))
        (-2 * p * ((‖Y ij.1 - Y ij.2‖ ^ 2) ^ (-p - 1) *
          inner ℝ (Y ij.1 - Y ij.2) (V ij.1 - V ij.2))) 0 := by
    intro ij hij
    have hdiff := ((hγ ij.1).sub (hγ ij.2)).norm_sq
    have hne : γ 0 ij.1 - γ 0 ij.2 ≠ 0 := by
      rw [hγzero]
      exact sub_ne_zero.mpr (fun h => (ne_of_lt ((mem_energyPairs _).mp hij)) (hY.2 h))
    have hpow := hdiff.rpow_const (p := -p)
      (Or.inl (ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hne))))
    convert! hpow using 1
    simp only [Pi.sub_apply, hγzero]
    ring
  have hs := HasDerivAt.sum hterm
  convert! hs using 1
  · funext t
    simp only [Finset.sum_apply]
    exact energy_sq_pair_sum p (γ t)
  · rw [Finset.mul_sum]

set_option maxHeartbeats 3000000 in
lemma pair_tangent_sum (Y V : Fin 8 → ℝ³) (r : ℝ)
    (hV : ∀ i, inner ℝ (Y i) (V i) = 0) :
    (∑ ij ∈ energyPairs, (‖Y ij.1 - Y ij.2‖ ^ 2) ^ r *
      inner ℝ (Y ij.1 - Y ij.2) (V ij.1 - V ij.2)) =
    -∑ i : Fin 8, inner ℝ
      (∑ j : Fin 8 with j ≠ i, (‖Y i - Y j‖ ^ 2) ^ r • Y j) (V i) := by
  simp only [energyPairs, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  simp [Fin.sum_univ_succ, inner_sub_left, inner_sub_right, inner_add_left,
    inner_smul_left, hV, norm_sub_rev]
  ring

end SquareAntiprismVerification
