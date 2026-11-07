import AllS.Units.N_GI.N_derivative_stability.N_chart_derivative

noncomputable section
open Real
namespace Blueprint.Thomson.Tail.Implementation

def pairDerivative (q : TangentCoordinates) (i j : Fin 8) : TangentCoordinates →L[ℝ] ℝ :=
  2 • (innerSL ℝ (orthographicChart q i-orthographicChart q j)).comp
    (chartDerivative q i-chartDerivative q j)

theorem pair_hasFDerivAt (q : TangentCoordinates) (hq : ‖q‖<1) (i j : Fin 8) :
    HasFDerivAt (fun z=>squaredDistance (orthographicChart z) i j) (pairDerivative q i j) q :=
  ((derivative_stability_chart_derivative q hq i).sub
    (derivative_stability_chart_derivative q hq j)).norm_sq

theorem chartDerivative_orthogonal (q ξ : TangentCoordinates) (hq : ‖q‖<1) (i : Fin 8) :
    inner ℝ (orthographicChart q i) (chartDerivative q i ξ)=0 := by
  have hs := lt_of_lt_of_le (chartRoot_bounds q hq i).1 (chartRoot_bounds q hq i).2.1
  have hP : inner ℝ (packingReference i) (tangentVector ξ i)=0 := by
    rw [real_inner_comm];exact tangentVector_orthogonal ξ i
  change inner ℝ (chartRoot q i • packingReference i+tangentVector q i) (chartDerivative q i ξ)=0
  rw [chartDerivative_apply]
  simp only [inner_add_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right,
    hP,real_inner_self_eq_norm_sq,packingReference_norm,tangentVector_orthogonal]
  field_simp [hs.ne']
  <;> ring

theorem pairDerivative_apply (q ξ : TangentCoordinates) (hq : ‖q‖<1) (i j : Fin 8) :
    pairDerivative q i j ξ = -2*(inner ℝ (chartDerivative q i ξ) (orthographicChart q j)+
      inner ℝ (orthographicChart q i) (chartDerivative q j ξ)) := by
  simp only [pairDerivative,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sub_apply,innerSL_apply_apply,smul_eq_mul,inner_sub_left,inner_sub_right]
  rw [chartDerivative_orthogonal q ξ hq i,chartDerivative_orthogonal q ξ hq j,
    real_inner_comm (orthographicChart q j) (chartDerivative q i ξ)]
  ring

theorem pairDerivative_error_identity (q ξ : TangentCoordinates) (hq : ‖q‖<1) (i j : Fin 8) :
    pairDerivative q i j ξ-contactLinear ξ i j = -2*(
      inner ℝ (tangentVector ξ i) (orthographicChart q j-packingReference j)+
      inner ℝ (orthographicChart q i-packingReference i) (tangentVector ξ j)-
      (inner ℝ (tangentVector q i) (tangentVector ξ i)/chartRoot q i)*inner ℝ (packingReference i) (orthographicChart q j)-
      (inner ℝ (tangentVector q j) (tangentVector ξ j)/chartRoot q j)*inner ℝ (orthographicChart q i) (packingReference j)) := by
  rw [pairDerivative_apply q ξ hq]
  simp only [chartDerivative_apply,inner_sub_left,inner_sub_right,real_inner_smul_left,
    real_inner_smul_right,contactLinear]
  rw [real_inner_comm (packingReference j) (tangentVector ξ i)]
  ring

#print axioms pairDerivative_error_identity
end Blueprint.Thomson.Tail.Implementation
