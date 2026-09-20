import Lean_Code.Stationarity
import Lean_Code.SliceCovering

open Real Filter
noncomputable section
namespace SquareAntiprismVerification

lemma chart_smooth_sphere_near_zero :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z : InfinitesimalCoordinates, ‖z‖ < ε →
      ∀ i : Fin 8, ‖coordinateChart z i‖ = 1 ∧
        ContDiffAt ℝ 2 (fun q => coordinateChart q i) z := by
  have he : ∀ i : Fin 8, ∀ᶠ z : InfinitesimalCoordinates in nhds 0,
      ‖tangentVector z.1 z.2 i‖ < 1 ∧ ContDiffAt ℝ 2 (fun q => coordinateChart q i) z := by
    intro i
    have hc : ContinuousAt (fun z : InfinitesimalCoordinates => ‖tangentVector z.1 z.2 i‖) 0 :=
      (tangentVector_contDiff i).continuous.continuousAt.norm
    have hnorm : ∀ᶠ z : InfinitesimalCoordinates in nhds 0, ‖tangentVector z.1 z.2 i‖ < 1 :=
      hc.tendsto.eventually (eventually_lt_nhds (by simp))
    exact hnorm.and ((coordinateChart_contDiffAt i).eventually (by norm_num))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (Filter.eventually_all.mpr he)
  refine ⟨ε, hε, ?_⟩
  intro z hz i
  have hi := hball (by simpa [dist_zero_right] using hz) i
  exact ⟨coordinateChart_mem_sphere z i hi.1.le, hi.2⟩

theorem chart_stationarity_near_zero :
    ∃ ε : ℝ, 0 < ε ∧ ∀ p a : ℝ, a ∈ Set.Ioo (0 : ℝ) 1 → F (2 * p) a = 0 →
      ∀ z : InfinitesimalCoordinates, ‖z‖ < ε →
      Congruent (coordinateChart z) (X a) → fderiv ℝ (chartEnergy p) z = 0 := by
  obtain ⟨ε, hε, hlocal⟩ := chart_smooth_sphere_near_zero
  refine ⟨ε, hε, ?_⟩
  intro p a ha hF z hz hcong
  have hconfig : IsConfiguration (coordinateChart z) :=
    congruent_isConfiguration (congruent_symm hcong) (X_isConfiguration a ha)
  have henergy : ContDiffAt ℝ 2 (chartEnergy p) z := by
    apply chartEnergy_contDiffAt
    · intro ij hij
      exact (((hlocal z hz ij.1).2).sub (hlocal z hz ij.2).2).norm_sq ℝ
    · intro ij hij
      exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr
        (fun h => (ne_of_lt ((mem_energyPairs _).mp hij)) (hconfig.2 h))))
  apply ContinuousLinearMap.ext
  intro v
  let γ := fun t : ℝ => coordinateChart (z + t • v)
  have hline : HasDerivAt (fun t : ℝ => z + t • v) v 0 := by
    simpa using HasDerivAt.const_add z ((hasDerivAt_id (0 : ℝ)).smul_const v)
  have hγ : ∀ i, DifferentiableAt ℝ (fun t => γ t i) 0 := by
    intro i
    have h := ((hlocal z hz i).2).differentiableAt (by norm_num)
    have hcomp := (show DifferentiableAt ℝ (fun q => coordinateChart q i)
      (z + (0 : ℝ) • v) from by simpa using h).comp 0 hline.differentiableAt
    simpa [γ, Function.comp_def] using hcomp
  have hcongγ : Congruent (γ 0) (X a) := by simpa [γ] using hcong
  have hball : ∀ᶠ t : ℝ in nhds 0, ‖z + t • v‖ < ε :=
    hline.continuousAt.norm.tendsto.eventually (eventually_lt_nhds (by simpa using hz))
  have hsphere : ∀ᶠ t : ℝ in nhds 0, ∀ i, ‖γ t i‖ = 1 := by
    filter_upwards [hball] with t ht
    intro i
    exact (hlocal _ ht i).1
  have hzero := congruent_curve_stationary p a ha hF γ hcongγ hγ hsphere
  have hzero' : HasDerivAt (fun t : ℝ => chartEnergy p (z + t • v)) 0 0 := by
    simpa only [chartEnergy_eq, γ] using hzero
  have hd := (henergy.differentiableAt (by norm_num)).hasFDerivAt
  have hcomp := (show HasFDerivAt (chartEnergy p) (fderiv ℝ (chartEnergy p) z)
    (z + (0 : ℝ) • v) from by simpa using hd).comp_hasDerivAt (0 : ℝ) hline
  exact hcomp.unique hzero'

end SquareAntiprismVerification
