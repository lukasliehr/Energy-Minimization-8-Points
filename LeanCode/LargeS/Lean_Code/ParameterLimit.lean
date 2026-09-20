import Lean_Code.StationarityAlgebra
import Lean_Code.PackingLoss
import Lean_Code.SliceCovering

open Real Filter
noncomputable section
namespace SquareAntiprismVerification

lemma aStar_two_mul_distance_bound (p : ℝ) (hp : 0 < p) :
    |aStar (2 * p) - aInf| ≤ (tau * Real.log 28 / 2) / p := by
  have hsp : 0 < 2 * p := by positivity
  have ha := (aStar_spec (2 * p) hsp.le).1
  have hpair := pairwise_sublevel_bound p hp (X (aStar (2 * p)))
    (X_isConfiguration _ ha) (antiprism_sublevel _ hsp) 0 1 (by decide)
  rw [antiprism_sq_distance _ ha] at hpair
  norm_num [antiprismDistanceModel] at hpair
  have htau : 0 < tau := by unfold tau; linarith [aInf_mem_Ioo.2]
  have hgap := mul_le_mul_of_nonneg_left (one_sub_rpow_neg_div_le p) htau.le
  rw [abs_of_pos (sub_pos.mpr (aStar_gt_aInf (2 * p) hsp.le))]
  have heq : (tau * Real.log 28 / 2) / p = tau * (Real.log 28 / p) / 2 := by ring
  rw [heq]
  unfold dA at hpair
  have ht : tau = 2 * (1 - aInf) := rfl
  nlinarith

theorem aStar_two_mul_tendsto : Tendsto (fun p : ℝ => aStar (2 * p)) atTop (nhds aInf) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let C : ℝ := tau * Real.log 28 / 2
  refine Filter.eventually_atTop.mpr ⟨max 1 (C / ε + 1), ?_⟩
  intro p hp
  have hpone : 1 ≤ p := (le_max_left _ _).trans hp
  have hppos : 0 < p := zero_lt_one.trans_le hpone
  have hpC : C / ε < p := by linarith [(le_max_right 1 (C / ε + 1)).trans hp]
  have hC : C / p < ε := by
    apply (div_lt_iff₀ hppos).mpr
    have hh := (div_lt_iff₀ hε).mp hpC
    nlinarith
  rw [Real.dist_eq]
  exact (aStar_two_mul_distance_bound p hppos).trans_lt hC

lemma X_continuous : Continuous X := by
  have hX : X = Xc := by funext a; exact X_eq_Xc a
  rw [hX]
  unfold Xc r h
  fun_prop

theorem optimized_antiprism_tendsto :
    Tendsto (fun p : ℝ => X (aStar (2 * p))) atTop (nhds P) := by
  exact X_continuous.continuousAt.tendsto.comp aStar_two_mul_tendsto

theorem optimized_chart_representation (ε : ℝ) (hε : 0 < ε) :
    ∃ p₀ : ℝ, 0 < p₀ ∧ ∀ p ≥ p₀,
      ∃ q : InfinitesimalCoordinates, InContactGauge q ∧ ‖q‖ < ε ∧
        Congruent (X (aStar (2 * p))) (coordinateChart q) := by
  obtain ⟨δ, hδ, hcover⟩ := local_chart_covering ε hε
  have hnear := (Metric.tendsto_nhds.mp optimized_antiprism_tendsto) δ hδ
  obtain ⟨p₁, hp₁⟩ := Filter.eventually_atTop.mp hnear
  refine ⟨max 1 p₁, zero_lt_one.trans_le (le_max_left _ _), ?_⟩
  intro p hp
  have hpzero : 0 ≤ 2 * p := by
    have hpone : 1 ≤ p := (le_max_left _ _).trans hp
    linarith
  exact hcover _ (X_mem_unitSphere _ (aStar_spec _ hpzero).1)
    (hp₁ p ((le_max_right _ _).trans hp))

end SquareAntiprismVerification
