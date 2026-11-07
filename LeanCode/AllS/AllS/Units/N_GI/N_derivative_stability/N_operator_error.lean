import AllS.Units.N_GI.N_derivative_stability.N_row_error
import AllS.Units.N_GI.N_contact_spectrum.N_physical_unweighted

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def contactDerivativeMap (q : TangentCoordinates) : TangentCoordinates →L[ℝ] EuclideanSpace ℝ ContactIndex :=
  (show TangentCoordinates →ₗ[ℝ] EuclideanSpace ℝ ContactIndex from
    { toFun := fun ξ=>WithLp.toLp 2 (fun e=>pairDerivative q e.1 (contactNext e) ξ)
      map_add' := by intros;ext e;simp [contactLinear_add]
      map_smul' := by intros;ext e;simp }).toContinuousLinearMap

def referenceContactMap : TangentCoordinates →L[ℝ] EuclideanSpace ℝ ContactIndex :=
  (show TangentCoordinates →ₗ[ℝ] EuclideanSpace ℝ ContactIndex from
    { toFun := fun ξ=>WithLp.toLp 2 (fun e=>referencePairDerivative e.1 (contactNext e) ξ)
      map_add' := by intros;ext e;simp [contactLinear_add]
      map_smul' := by intros;ext e;simp }).toContinuousLinearMap

@[simp] theorem contactDerivativeMap_apply (q ξ : TangentCoordinates) (e : ContactIndex) :
    contactDerivativeMap q ξ e=pairDerivative q e.1 (contactNext e) ξ := rfl
@[simp] theorem referenceContactMap_apply (ξ : TangentCoordinates) (e : ContactIndex) :
    referenceContactMap ξ e=contactLinear ξ e.1 (contactNext e) := referencePairDerivative_apply ξ _ _

theorem contact_incident_unweighted (u : Fin 8→ℝ) :
    (∑ e : ContactIndex, (u e.1+u (contactNext e)))=4*(∑ i, u i) := by
  norm_num [Fintype.sum_prod_type,Fin.sum_univ_succ,contactNext,Fin.add_def,Fin.succ]
  ring

theorem contact_derivative_error_sq (q ξ : TangentCoordinates) (hq : ‖q‖≤3/10) :
    ‖(contactDerivativeMap q-referenceContactMap) ξ‖^2≤144*‖q‖^2*‖ξ‖^2 := by
  have hq1 : ‖q‖<1 := by linarith
  have hs := (chart_metric_bounds q hq).2.2.2
  have hroot := (chartRoot_bounds q hq1 0).1
  have hpos : 0≤chartStretch ‖q‖+1/chartMinRoot ‖q‖ := by
    have := chartStretch_nonneg ‖q‖
    positivity
  have hpoint (e : ContactIndex) :
      (pairDerivative q e.1 (contactNext e) ξ-contactLinear ξ e.1 (contactNext e))^2≤
      36*(‖tangentVector q e.1‖^2+‖tangentVector q (contactNext e)‖^2)*‖ξ‖^2 := by
    have h := pair_error_sq q ξ hq1 e.1 (contactNext e)
    have hm := mul_le_mul_of_nonneg_left (tangentVector_pair_norm_sq ξ e.1 (contactNext e) (contactNext_ne e))
      (show 0≤4*(chartStretch ‖q‖+1/chartMinRoot ‖q‖)^2*
        (‖tangentVector q e.1‖^2+‖tangentVector q (contactNext e)‖^2) by positivity)
    have hc : 4*(chartStretch ‖q‖+1/chartMinRoot ‖q‖)^2≤36 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc
      (show 0≤‖tangentVector q e.1‖^2+‖tangentVector q (contactNext e)‖^2 by positivity)) (sq_nonneg ‖ξ‖)
    exact (h.trans hm).trans hmul
  rw [EuclideanSpace.norm_sq_eq]
  simp only [ContinuousLinearMap.sub_apply,PiLp.sub_apply,contactDerivativeMap_apply,
    referenceContactMap_apply,Real.norm_eq_abs,sq_abs]
  calc
    _ ≤ ∑ e : ContactIndex, 36*(‖tangentVector q e.1‖^2+‖tangentVector q (contactNext e)‖^2)*‖ξ‖^2 :=
      Finset.sum_le_sum (fun e _=>hpoint e)
    _ = 36*(4*‖q‖^2)*‖ξ‖^2 := by
      rw [←Finset.sum_mul,←Finset.mul_sum,contact_incident_unweighted (fun i=>‖tangentVector q i‖^2),tangentVector_sum_norm_sq]
    _ = _ := by ring

theorem derivative_stability_operator_error (q : TangentCoordinates) (hq : ‖q‖≤3/10) :
    ‖contactDerivativeMap q-referenceContactMap‖≤12*‖q‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro ξ
  have h := contact_derivative_error_sq q ξ hq
  have hp : 0≤12*‖q‖*‖ξ‖ := by positivity
  nlinarith [norm_nonneg ((contactDerivativeMap q-referenceContactMap) ξ)]

#print axioms derivative_stability_operator_error
end Blueprint.Thomson.Tail.Implementation
