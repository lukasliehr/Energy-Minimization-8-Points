import Lean_Code.PackingLoss

open Real Filter
noncomputable section
namespace SquareAntiprismVerification

def chartPairDistance (q : InfinitesimalCoordinates) (ij : Fin 8 × Fin 8) : ℝ :=
  ‖coordinateChart q ij.1 - coordinateChart q ij.2‖ ^ 2

lemma chartPairDistance_contDiffAt (ij : Fin 8 × Fin 8) :
    ContDiffAt ℝ 2 (fun q => chartPairDistance q ij) 0 := by
  exact ((coordinateChart_contDiffAt ij.1).sub
    (coordinateChart_contDiffAt ij.2)).norm_sq ℝ

lemma finite_continuous_bound_at_zero {ι F : Type} [Fintype ι]
    [NormedAddCommGroup F] (f : ι → InfinitesimalCoordinates → F)
    (hf : ∀ i, ContinuousAt (f i) 0) :
    ∃ M ε : ℝ, 0 < M ∧ 0 < ε ∧ ∀ z : InfinitesimalCoordinates,
      ‖z‖ < ε → ∀ i, ‖f i z‖ ≤ M := by
  let M : ℝ := 1 + ∑ i, ‖f i 0‖
  have hM : 0 < M := by
    dsimp [M]
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (Finset.sum_nonneg (fun i hi => norm_nonneg _))
  have he : ∀ i, ∀ᶠ z : InfinitesimalCoordinates in nhds 0,
      ‖f i z - f i 0‖ < 1 := by
    intro i
    simpa [dist_eq_norm] using (Metric.tendsto_nhds.mp (hf i)) 1 zero_lt_one
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (Filter.eventually_all.mpr he)
  refine ⟨M, ε, hM, hε, ?_⟩
  intro z hz i
  have hnear := hball (by simpa [dist_zero_right] using hz) i
  have hsum : ‖f i 0‖ ≤ ∑ j, ‖f j 0‖ :=
    Finset.single_le_sum (f := fun j => ‖f j 0‖)
      (fun j hj => norm_nonneg (f j 0)) (Finset.mem_univ i)
  have hnorm := norm_sub_norm_le (f i z) (f i 0)
  dsimp [M]
  linarith

/-- Uniform operator-norm bounds for the first and second derivatives of
all sixty-four labeled squared distances; diagonal pairs cause no problem. -/
theorem chart_pair_derivative_bounds :
    ∃ L M ε : ℝ, 0 < L ∧ 0 < M ∧ 0 < ε ∧
      ∀ z : InfinitesimalCoordinates, ‖z‖ < ε → ∀ ij : Fin 8 × Fin 8,
        ‖fderiv ℝ (fun q => chartPairDistance q ij) z‖ ≤ L ∧
        ‖fderiv ℝ (fderiv ℝ (fun q => chartPairDistance q ij)) z‖ ≤ M := by
  obtain ⟨L, ε₁, hL, hε₁, hfirst⟩ := finite_continuous_bound_at_zero
    (fun ij z => fderiv ℝ (fun q => chartPairDistance q ij) z)
    (fun ij => (chartPairDistance_contDiffAt ij).continuousAt_fderiv (by norm_num))
  have hsecondCont : ∀ ij : Fin 8 × Fin 8,
      ContinuousAt (fderiv ℝ (fderiv ℝ (fun q => chartPairDistance q ij))) 0 := by
    intro ij
    have h : ContDiffAt ℝ 1 (fderiv ℝ (fun q => chartPairDistance q ij)) 0 :=
      (chartPairDistance_contDiffAt ij).fderiv_right (by norm_num)
    exact h.continuousAt_fderiv (by norm_num)
  obtain ⟨M, ε₂, hM, hε₂, hsecond⟩ := finite_continuous_bound_at_zero
    (fun ij z => fderiv ℝ (fderiv ℝ (fun q => chartPairDistance q ij)) z) hsecondCont
  refine ⟨L, M, min ε₁ ε₂, hL, hM, lt_min hε₁ hε₂, ?_⟩
  intro z hz ij
  exact ⟨hfirst z (hz.trans_le (min_le_left _ _)) ij,
    hsecond z (hz.trans_le (min_le_right _ _)) ij⟩

lemma chartPairDistance_second_bound {M : ℝ} (z v : InfinitesimalCoordinates)
    (ij : Fin 8 × Fin 8)
    (hM : ‖fderiv ℝ (fderiv ℝ (fun q => chartPairDistance q ij)) z‖ ≤ M) :
    |fderiv ℝ (fderiv ℝ (fun q => chartPairDistance q ij)) z v v| ≤ M * ‖v‖ ^ 2 := by
  let H := fderiv ℝ (fderiv ℝ (fun q => chartPairDistance q ij)) z
  have h₁ := (H v).le_opNorm v
  have h₂ := H.le_opNorm v
  have h₃ := mul_le_mul_of_nonneg_right hM (norm_nonneg v)
  have h₄ := mul_le_mul_of_nonneg_right (h₂.trans h₃) (norm_nonneg v)
  have h := h₁.trans h₄
  simpa [H, Real.norm_eq_abs, pow_two, mul_assoc] using h

lemma chart_pair_smooth_near_zero :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : InfinitesimalCoordinates, ‖z‖ < ε →
      ∀ ij : Fin 8 × Fin 8, ContDiffAt ℝ 2 (fun q => chartPairDistance q ij) z := by
  have he : ∀ ij : Fin 8 × Fin 8, ∀ᶠ z : InfinitesimalCoordinates in nhds 0,
      ContDiffAt ℝ 2 (fun q => chartPairDistance q ij) z := by
    intro ij
    exact (chartPairDistance_contDiffAt ij).eventually (by norm_num)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (Filter.eventually_all.mpr he)
  exact ⟨ε, hε, fun z hz => hball (by simpa [dist_zero_right] using hz)⟩

/-- A common neighborhood with the Lipschitz and second-derivative bounds
needed for the energy Hessian.  All constants are independent of the exponent. -/
theorem chart_pair_local_estimates :
    ∃ L M ε : ℝ, 0 < L ∧ 0 < M ∧ 0 < ε ∧
      ∀ z : InfinitesimalCoordinates, ‖z‖ < ε → ∀ ij : Fin 8 × Fin 8,
        ContDiffAt ℝ 2 (fun q => chartPairDistance q ij) z ∧
        |chartPairDistance z ij - chartPairDistance 0 ij| ≤ L * ‖z‖ ∧
        ∀ v : InfinitesimalCoordinates,
          |fderiv ℝ (fderiv ℝ (fun q => chartPairDistance q ij)) z v v|
            ≤ M * ‖v‖ ^ 2 := by
  obtain ⟨L, M, ε₁, hL, hM, hε₁, hderiv⟩ := chart_pair_derivative_bounds
  obtain ⟨ε₂, hε₂, hsmooth⟩ := chart_pair_smooth_near_zero
  let ε := min ε₁ ε₂
  have hε : 0 < ε := lt_min hε₁ hε₂
  refine ⟨L, M, ε, hL, hM, hε, ?_⟩
  intro z hz ij
  have hz₁ : ‖z‖ < ε₁ := hz.trans_le (min_le_left _ _)
  have hz₂ : ‖z‖ < ε₂ := hz.trans_le (min_le_right _ _)
  refine ⟨hsmooth z hz₂ ij, ?_, fun v =>
    chartPairDistance_second_bound z v ij (hderiv z hz₁ ij).2⟩
  have hd : ∀ q ∈ Metric.ball (0 : InfinitesimalCoordinates) ε,
      DifferentiableAt ℝ (fun q => chartPairDistance q ij) q := by
    intro q hq
    have hqn : ‖q‖ < ε := by simpa [Metric.mem_ball, dist_zero_right] using hq
    exact (hsmooth q (hqn.trans_le (min_le_right _ _)) ij).differentiableAt (by norm_num)
  have hb : ∀ q ∈ Metric.ball (0 : InfinitesimalCoordinates) ε,
      ‖fderiv ℝ (fun q => chartPairDistance q ij) q‖ ≤ L := by
    intro q hq
    have hqn : ‖q‖ < ε := by simpa [Metric.mem_ball, dist_zero_right] using hq
    exact (hderiv q (hqn.trans_le (min_le_left _ _)) ij).1
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le hd hb (convex_ball 0 ε)
    (x := 0) (y := z) (by simpa using hε)
    (by simpa [Metric.mem_ball, dist_zero_right] using hz)
  simpa [Real.norm_eq_abs] using h

lemma contact_fderiv_uniform_variation (c : ℝ) (hc : 0 < c) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : InfinitesimalCoordinates, ‖z‖ < ε →
      ∀ e : Fin 16,
        ‖fderiv ℝ (fun q => chartContactDistance q e) z -
          fderiv ℝ (fun q => chartContactDistance q e) 0‖ < c := by
  have he : ∀ e : Fin 16, ∀ᶠ z : InfinitesimalCoordinates in nhds 0,
      ‖fderiv ℝ (fun q => chartContactDistance q e) z -
        fderiv ℝ (fun q => chartContactDistance q e) 0‖ < c := by
    intro e
    have hcont := (chartContactDistance_contDiffAt e).continuousAt_fderiv (by norm_num)
    simpa [dist_eq_norm] using (Metric.tendsto_nhds.mp hcont) c hc
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (Filter.eventually_all.mpr he)
  exact ⟨ε, hε, fun z hz => hball (by simpa [dist_zero_right] using hz)⟩

/-- Contact rank persists uniformly throughout a neighborhood of the origin. -/
theorem chart_contact_rank_uniform :
    ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧ ∀ z : InfinitesimalCoordinates, ‖z‖ < ε →
      ∀ v : InfinitesimalCoordinates, InContactGauge v →
        ∃ e : Fin 16, c * ‖v‖ ≤
          |fderiv ℝ (fun q => chartContactDistance q e) z v| := by
  obtain ⟨c, hc, hrow⟩ := uniform_positive_contactRow
  obtain ⟨ε, hε, hvar⟩ := contact_fderiv_uniform_variation c hc
  refine ⟨c, ε, hc, hε, ?_⟩
  intro z hz v hv
  obtain ⟨e, he⟩ := hrow v hv
  refine ⟨e, ?_⟩
  have herror := (fderiv ℝ (fun q => chartContactDistance q e) z -
    fderiv ℝ (fun q => chartContactDistance q e) 0).le_opNorm v
  have hbound := mul_le_mul_of_nonneg_right (hvar z hz e).le (norm_nonneg v)
  have herror' : |fderiv ℝ (fun q => chartContactDistance q e) z v +
      2 * contactRows v e| ≤ c * ‖v‖ := by
    simpa [ContinuousLinearMap.sub_apply, chartContactDistance_fderiv,
      Real.norm_eq_abs, sub_neg_eq_add] using herror.trans hbound
  have hu := (abs_le.mp herror').2
  have hn := neg_le_abs (fderiv ℝ (fun q => chartContactDistance q e) z v)
  linarith

end SquareAntiprismVerification
