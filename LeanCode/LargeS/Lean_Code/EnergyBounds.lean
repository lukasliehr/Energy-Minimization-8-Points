import Lean_Code.BestPacking

open Real
noncomputable section
namespace SquareAntiprismVerification
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

lemma rpow_neg_le_rpow_neg_of_le {x y p : ℝ} (hx : 0 < x) (hxy : x ≤ y)
    (hp : 0 < p) : y ^ (-p) ≤ x ^ (-p) := by
  have hy : 0 < y := hx.trans_le hxy
  rw [Real.rpow_neg (le_of_lt hx), Real.rpow_neg (le_of_lt hy)]
  exact (inv_le_inv₀ (Real.rpow_pos_of_pos hy p)
    (Real.rpow_pos_of_pos hx p)).2
    (Real.rpow_le_rpow (le_of_lt hx) hxy (le_of_lt hp))

lemma norm_rpow_two_mul (v : ℝ³) (p : ℝ) :
    ‖v‖ ^ (-(2 * p)) = (‖v‖ ^ 2) ^ (-p) := by
  calc
    ‖v‖ ^ (-(2 * p)) = (√(‖v‖ ^ 2)) ^ (-(2 * p)) := by
      rw [Real.sqrt_sq (norm_nonneg v)]
    _ = (‖v‖ ^ 2) ^ (-(2 * p) / 2) :=
      sqrt_rpow_neg (‖v‖ ^ 2) (2 * p) (sq_nonneg ‖v‖)
    _ = (‖v‖ ^ 2) ^ (-p) := by ring_nf

lemma energy_P_le (p : ℝ) (hp : 0 < p) :
    E (2 * p) P ≤ 28 * tau ^ (-p) := by
  unfold E
  calc
    (∑ i : Fin 8, ∑ j : Fin 8 with i < j, ‖P i - P j‖ ^ (-(2 * p))) ≤
        ∑ i : Fin 8, ∑ j : Fin 8 with i < j, tau ^ (-p) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hij : i < j := by simpa using hj
      rw [norm_rpow_two_mul]
      exact rpow_neg_le_rpow_neg_of_le
        (by unfold tau; linarith [aInf_mem_Ioo.2])
        (P_pair_sq_ge_tau i j (ne_of_lt hij)) hp
    _ = 28 * tau ^ (-p) := by
      rw [finEight_pair_sum]
      ring

lemma energy_pair_term_le (p : ℝ) (Y : Fin 8 → ℝ³) {i j : Fin 8}
    (hij : i < j) : ‖Y i - Y j‖ ^ (-(2 * p)) ≤ E (2 * p) Y := by
  unfold E
  have hinner : ‖Y i - Y j‖ ^ (-(2 * p)) ≤
      ∑ k : Fin 8 with i < k, ‖Y i - Y k‖ ^ (-(2 * p)) := by
    exact Finset.single_le_sum
      (f := fun k : Fin 8 => ‖Y i - Y k‖ ^ (-(2 * p)))
      (s := Finset.univ.filter fun k : Fin 8 => i < k)
      (fun k hk => Real.rpow_nonneg (norm_nonneg _) _) (by simpa using hij)
  have houter : (∑ k : Fin 8 with i < k, ‖Y i - Y k‖ ^ (-(2 * p))) ≤
      ∑ l : Fin 8, ∑ k : Fin 8 with l < k, ‖Y l - Y k‖ ^ (-(2 * p)) := by
    exact Finset.single_le_sum
      (f := fun l : Fin 8 =>
        ∑ k : Fin 8 with l < k, ‖Y l - Y k‖ ^ (-(2 * p)))
      (s := Finset.univ)
      (fun l hl => Finset.sum_nonneg fun k hk =>
        Real.rpow_nonneg (norm_nonneg _) _) (by simp)
  exact hinner.trans houter

/-- Paper Lemma 6.1: every squared distance on the antiprism sublevel is
bounded from below by `tau * 28⁻¹ᐟᵖ`. -/
theorem pairwise_sublevel_bound (p : ℝ) (hp : 0 < p)
    (Y : Fin 8 → ℝ³) (hY : IsConfiguration Y)
    (hsub : E (2 * p) Y ≤ E (2 * p) P) (i j : Fin 8) (hij : i ≠ j) :
    tau * (28 : ℝ) ^ (-1 / p) ≤ ‖Y i - Y j‖ ^ 2 := by
  have htau : 0 < tau := by unfold tau; linarith [aInf_mem_Ioo.2]
  have ordered_bound : ∀ {u v : Fin 8}, u < v →
      tau * (28 : ℝ) ^ (-1 / p) ≤ ‖Y u - Y v‖ ^ 2 := by
    intro u v huv
    have hterm := energy_pair_term_le p Y huv
    have hbound : ‖Y u - Y v‖ ^ (-(2 * p)) ≤ 28 * tau ^ (-p) :=
      hterm.trans (hsub.trans (energy_P_le p hp))
    rw [norm_rpow_two_mul] at hbound
    have hne : Y u ≠ Y v := fun h => (ne_of_lt huv) (hY.2 h)
    have hnorm : 0 < ‖Y u - Y v‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    have hdpos : 0 < ‖Y u - Y v‖ ^ 2 := sq_pos_of_pos hnorm
    have hkpos : 0 < (28 : ℝ) ^ (-1 / p) :=
      Real.rpow_pos_of_pos (by norm_num) _
    by_contra hgoal
    have hlt : ‖Y u - Y v‖ ^ 2 < tau * (28 : ℝ) ^ (-1 / p) :=
      lt_of_not_ge hgoal
    have hrev := rpow_neg_lt_rpow_neg hdpos hlt hp
    have hkpow : ((28 : ℝ) ^ (-1 / p)) ^ (-p) = 28 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 28)]
      have hpexp : (-1 / p) * (-p) = 1 := by field_simp
      rw [hpexp, Real.rpow_one]
    have heval : (tau * (28 : ℝ) ^ (-1 / p)) ^ (-p) =
        28 * tau ^ (-p) := by
      rw [Real.mul_rpow (le_of_lt htau) (le_of_lt hkpos), hkpow]
      ring
    rw [heval] at hrev
    linarith
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact ordered_bound hijlt
  · have hbound := ordered_bound hjilt
    have hv : Y j - Y i = -(Y i - Y j) := by abel
    rw [hv, norm_neg] at hbound
    exact hbound

end SquareAntiprismVerification
