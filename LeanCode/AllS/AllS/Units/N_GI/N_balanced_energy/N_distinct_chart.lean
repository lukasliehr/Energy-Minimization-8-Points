import AllS.Units.N_GI.N_constants.N_pair_table
import AllS.Units.N_GI.N_contact_taylor.N_radical_bounds
import AllS.Units.N_GI.N_nearest_chart.N_chart_unit

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

theorem chart_deviation_sq (q : TangentCoordinates) (hq : ‖q‖ < 1) (i : Fin 8) :
    ‖orthographicChart q i-packingReference i‖^2=2*(1-chartRoot q i) := by
  have hi : inner ℝ (orthographicChart q i) (packingReference i)=chartRoot q i := by
    change inner ℝ (chartRoot q i • packingReference i+tangentVector q i) (packingReference i)=_
    rw [inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq,
      packingReference_norm,tangentVector_orthogonal]
    ring
  rw [norm_sub_sq_real,nearest_chart_chart_unit q hq i,packingReference_norm,hi]
  ring

theorem chart_deviation_sq_le (q : TangentCoordinates) (hq : ‖q‖ < 1) (i : Fin 8) :
    ‖orthographicChart q i-packingReference i‖^2 ≤ 2*‖tangentVector q i‖^2 := by
  rw [chart_deviation_sq q hq i]
  obtain ⟨hs,hi,hupper⟩ := chartRoot_bounds q hq i
  have hroot := chartRoot_sq q hq i
  have hprod : 0 ≤ chartRoot q i*(1-chartRoot q i) := mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem chart_deviation_pair_le (q : TangentCoordinates) (hq : ‖q‖ < 1)
    (i j : Fin 8) (hij : i ≠ j) :
    ‖orthographicChart q i-packingReference i‖+‖orthographicChart q j-packingReference j‖ ≤ 2*‖q‖ := by
  have hi := chart_deviation_sq_le q hq i
  have hj := chart_deviation_sq_le q hq j
  have hp := tangentVector_pair_norm_sq q i j hij
  have hdiff := sq_nonneg (‖orthographicChart q i-packingReference i‖-‖orthographicChart q j-packingReference j‖)
  nlinarith [norm_nonneg q,norm_nonneg (orthographicChart q i-packingReference i),
    norm_nonneg (orthographicChart q j-packingReference j)]

theorem packingReference_distance_gt_one (i j : Fin 8) (hij : i ≠ j) :
    1 < ‖packingReference i-packingReference j‖ := by
  have hsq := norm_sub_sq_real (packingReference i) (packingReference j)
  rw [packingReference_norm,packingReference_norm,packingReference_inner_cyclic,if_neg hij] at hsq
  have ha := constants_algebra
  split_ifs at hsq <;> nlinarith [norm_nonneg (packingReference i-packingReference j)]

theorem balanced_energy_distinct_chart (q : TangentCoordinates) (hq : ‖q‖ ≤ 3/10) :
    IsConfiguration (orthographicChart q) ∧
    ∀ i j : Fin 8, i ≠ j → 2/5 < ‖orthographicChart q i-orthographicChart q j‖ := by
  have hq1 : ‖q‖ < 1 := by linarith
  have hsep : ∀ i j : Fin 8, i ≠ j → 2/5 < ‖orthographicChart q i-orthographicChart q j‖ := by
    intro i j hij
    have hP := packingReference_distance_gt_one i j hij
    have he := chart_deviation_pair_le q hq1 i j hij
    have ht : ‖packingReference i-packingReference j‖ ≤
        ‖orthographicChart q i-packingReference i‖+
        ‖orthographicChart q i-orthographicChart q j‖+
        ‖orthographicChart q j-packingReference j‖ := by
      calc
        _ = ‖(packingReference i-orthographicChart q i)+
          (orthographicChart q i-orthographicChart q j)+(orthographicChart q j-packingReference j)‖ := by congr 1 <;> module
        _ ≤ (‖packingReference i-orthographicChart q i‖+
            ‖orthographicChart q i-orthographicChart q j‖)+
            ‖orthographicChart q j-packingReference j‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
        _ = _ := by rw [norm_sub_rev (packingReference i) (orthographicChart q i)]
    linarith
  refine ⟨⟨nearest_chart_chart_unit q hq1,?_⟩,hsep⟩
  intro i j he
  by_contra hij
  have h := hsep i j hij
  rw [he,sub_self,norm_zero] at h
  norm_num at h

#print axioms balanced_energy_distinct_chart
end Blueprint.Thomson.Tail.Implementation
