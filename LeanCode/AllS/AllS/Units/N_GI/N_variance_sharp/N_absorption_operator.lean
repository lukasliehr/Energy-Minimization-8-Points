import AllS.Units.N_GI.N_variance_sharp.N_physical_tensor_bridge
import AllS.Units.N_GI.N_contact_spectrum.N_rotation_kernel
import AllS.Units.N_GI.N_centered_quadratic.N_projected_identity

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def varianceContactVector (e : ContactIndex) : TangentCoordinates :=
  (-2*packingRadius) • (localEvaluation e.1 (contactSine e.2)
      (packingZHeight*contactMeridianFactor e.2)+
    localEvaluation (contactNext e) (-contactSine e.2)
      (packingZHeight*contactMeridianFactor e.2))

theorem varianceContactVector_inner (q : TangentCoordinates) (e : ContactIndex) :
    inner ℝ q (varianceContactVector e)=contactLinearArray q e := by
  rw [varianceContactVector,real_inner_smul_right,inner_add_right,localEvaluation_inner,
    localEvaluation_inner]
  unfold contactLinearArray
  rw [contactLinear_cyclic_formula]
  ring

def varianceGramOperator : TangentCoordinates →ₗ[ℝ] TangentCoordinates where
  toFun q := ∑e : ContactIndex,(contactWeight e*contactLinearArray q e) • varianceContactVector e
  map_add' q v := by
    simp only [contactLinearArray,contactLinear_add,mul_add,add_smul,Finset.sum_add_distrib]
  map_smul' c q := by
    simp only [contactLinearArray,contactLinear_smul_spectrum,Finset.smul_sum,smul_smul,RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro e _
    congr 1
    ring

def varianceRotationOperator : TangentCoordinates →ₗ[ℝ] TangentCoordinates where
  toFun := rotationProjection
  map_add' q v := by simp [rotationProjection,inner_add_right,add_smul,Finset.sum_add_distrib]
  map_smul' c q := by
    simp [rotationProjection,real_inner_smul_right,Finset.smul_sum,smul_smul,mul_comm]

def varianceAbsorptionOperator : TangentCoordinates →ₗ[ℝ] TangentCoordinates :=
  varianceGramOperator-(17/5:ℝ) • LinearMap.id+(22/5:ℝ) • varianceRotationOperator

theorem varianceAbsorptionOperator_inner (q v : TangentCoordinates) :
    inner ℝ q (varianceAbsorptionOperator v)=
      (∑e : ContactIndex,contactWeight e*contactLinearArray q e*contactLinearArray v e)-
      (17/5:ℝ)*inner ℝ q v+(22/5:ℝ)*
        (∑j : Fin 3,inner ℝ (normalizedRotation j) q*inner ℝ (normalizedRotation j) v) := by
  change inner ℝ q ((∑e : ContactIndex,(contactWeight e*contactLinearArray v e) • varianceContactVector e)-
    (17/5:ℝ) • v+(22/5:ℝ) • rotationProjection v)=_
  simp only [inner_add_right,inner_sub_right,real_inner_smul_right,inner_sum,
    varianceContactVector_inner,rotationProjection,real_inner_comm q (normalizedRotation _)]
  congr 2
  · apply Finset.sum_congr rfl
    intro e _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

theorem varianceAbsorptionOperator_symmetric (q v : TangentCoordinates) :
    inner ℝ q (varianceAbsorptionOperator v)=inner ℝ v (varianceAbsorptionOperator q) := by
  rw [varianceAbsorptionOperator_inner,varianceAbsorptionOperator_inner,real_inner_comm v q]
  congr 2
  · apply Finset.sum_congr rfl
    intro e _; ring
  · apply Finset.sum_congr rfl
    intro j _; ring

theorem varianceAbsorptionOperator_quad (q : TangentCoordinates) (hq : q∈rotationSlice) :
    inner ℝ q (varianceAbsorptionOperator q)=
      (∑e : ContactIndex,contactWeight e*(contactLinearArray q e)^2)-(17/5:ℝ)*‖q‖^2 := by
  rw [varianceAbsorptionOperator_inner,real_inner_self_eq_norm_sq]
  have hz := (mem_rotationSlice_iff_normalized q).mp hq
  simp only [hz,zero_mul,Finset.sum_const_zero,mul_zero,add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro e _; ring

theorem varianceAbsorptionOperator_nonnegative (q : TangentCoordinates) :
    0 ≤ inner ℝ q (varianceAbsorptionOperator q) := by
  have hs := contact_spectrum_physical_weighted (sliceProjection q) (sliceProjection_mem q)
  simp only [contactLinear_sliceProjection] at hs
  change (59546/15625:ℝ)*‖sliceProjection q‖^2≤
    ∑e : ContactIndex,contactWeight e*(contactLinearArray q e)^2 at hs
  have hn := sliceProjection_norm_sq q
  have hr := rotationProjection_norm_sq q
  rw [varianceAbsorptionOperator_inner,real_inner_self_eq_norm_sq]
  have he : (∑e : ContactIndex,contactWeight e*contactLinearArray q e*contactLinearArray q e)=
      ∑e : ContactIndex,contactWeight e*(contactLinearArray q e)^2 := by
    apply Finset.sum_congr rfl
    intro e _; ring
  rw [he]
  have hp : (∑j : Fin 3,inner ℝ (normalizedRotation j) q*inner ℝ (normalizedRotation j) q)=
      ∑j : Fin 3,(inner ℝ (normalizedRotation j) q)^2 := by simp only [pow_two]
  rw [hp]
  nlinarith [sq_nonneg ‖sliceProjection q‖,sq_nonneg ‖rotationProjection q‖]

#print axioms varianceAbsorptionOperator_quad
#print axioms varianceAbsorptionOperator_nonnegative
end Blueprint.Thomson.Tail.Implementation
