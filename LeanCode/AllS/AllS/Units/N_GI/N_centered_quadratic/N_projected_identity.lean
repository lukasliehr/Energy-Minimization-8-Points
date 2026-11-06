import AllS.Units.N_GI.N_centered_quadratic.N_stress_rotation
import AllS.Units.N_GI.N_variance_basic.N_centering_projection

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem sliceProjection_sub (q v : TangentCoordinates) : sliceProjection (q-v)=sliceProjection q-sliceProjection v := by
  simp [sliceProjection,rotationProjection,inner_sub_right,sub_smul,Finset.sum_sub_distrib]
  abel

theorem sliceProjection_smul (c : ℝ) (q : TangentCoordinates) : sliceProjection (c • q)=c • sliceProjection q := by
  simp [sliceProjection,rotationProjection,real_inner_smul_right,mul_smul,Finset.smul_sum,smul_sub]

def contactMeanM (q : TangentCoordinates) : TangentCoordinates := contactTotalWeight⁻¹ • stressMap q

theorem contactMeanM_mem (q : TangentCoordinates) : contactMeanM q∈rotationSlice :=
  rotationSlice.smul_mem _ (stressMap_mem_rotationSlice q)

theorem centeredContact_projected_norm (q : TangentCoordinates) :
    (∑e : ContactIndex,contactWeight e*‖sliceProjection (contactM e q-contactMeanM q)‖^2)=centeredContactGram q q := by
  have hW := contactTotalWeight_pos.ne'
  have hc (e : ContactIndex) : sliceProjection (contactM e q-contactMeanM q)=
      sliceProjection (contactM e q)-contactMeanM q := by
    rw [sliceProjection_sub,sliceProjection_eq_self _ (contactMeanM_mem q)]
  have hcross : (∑e : ContactIndex,contactWeight e*inner ℝ (sliceProjection (contactM e q)) (stressMap q))=‖stressMap q‖^2 := by
    have ht (e : ContactIndex) : inner ℝ (sliceProjection (contactM e q)) (stressMap q)=inner ℝ (stressMap q) (contactM e q) := by
      rw [real_inner_comm,sliceProjection_inner _ _ (stressMap_mem_rotationSlice q)]
    simp_rw [ht]
    change (∑e,contactWeight e*inner ℝ (stressMap q) (contactM e q))=‖stressMap q‖^2
    calc
      _ = inner ℝ (stressMap q) (stressMap q) := by
        change (∑e,contactWeight e*inner ℝ (stressMap q) (contactM e q))=
          inner ℝ (stressMap q) (∑e,contactWeight e • contactM e q)
        rw [inner_sum]
        simp only [real_inner_smul_right]
      _ = _ := real_inner_self_eq_norm_sq _
  simp_rw [hc,norm_sub_sq_real,contactMeanM,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    real_inner_smul_right]
  rw [centeredContactGram_self]
  simp only [mul_sub,mul_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  rw [← Finset.sum_mul,contactWeight_sum]
  have hcross' : (∑e : ContactIndex,contactWeight e*(2*(contactTotalWeight⁻¹*inner ℝ (sliceProjection (contactM e q)) (stressMap q))))=
      2*contactTotalWeight⁻¹*‖stressMap q‖^2 := by
    rw [← hcross,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring
  rw [hcross']
  field_simp
  ring

theorem centered_quadratic_centered_norm_identity (q : TangentCoordinates) :
    (∑e : ContactIndex,contactWeight e*‖sliceProjection (contactM e q-contactMeanM q)‖^2)=
      (∑e : ContactIndex,contactWeight e*‖sliceProjection (contactM e q)‖^2)-‖stressMap q‖^2/contactTotalWeight :=
  (centeredContact_projected_norm q).trans (centeredContactGram_self q)

/-- The full-space Q of L.7, retaining its middle slice projector. -/
def centeredQMap (v : TangentCoordinates) : TangentCoordinates :=
  (∑e : ContactIndex,contactWeight e • contactM e (sliceProjection (contactM e v)))-
    contactTotalWeight⁻¹ • stressMap (stressMap v)

def centeredSliceQMap (v : TangentCoordinates) : TangentCoordinates :=
  sliceProjection (centeredQMap (sliceProjection v))

theorem sliceProjection_inner_full (q v : TangentCoordinates) :
    inner ℝ q (sliceProjection v)=inner ℝ q v-
      ∑j : Fin 3,inner ℝ (normalizedRotation j) q*inner ℝ (normalizedRotation j) v := by
  simp only [sliceProjection,rotationProjection,inner_sub_right,inner_sum,real_inner_smul_right]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [real_inner_comm q (normalizedRotation j)]
  ring

theorem centeredQMap_inner (q v : TangentCoordinates) : inner ℝ q (centeredQMap v)=centeredContactGram q v := by
  have hM (e : ContactIndex) : inner ℝ q (contactM e (sliceProjection (contactM e v)))=
      inner ℝ (contactM e q) (sliceProjection (contactM e v)) := by
    rw [contactM_symmetric,real_inner_comm]
  have hH : inner ℝ q (stressMap (stressMap v))=inner ℝ (stressMap q) (stressMap v) := by
    rw [stressMap_inner,stressMap_inner_symm]
  simp only [centeredQMap,inner_sub_right,inner_sum,real_inner_smul_right,hM,sliceProjection_inner_full,hH]
  rw [meanTangent_parseval]
  simp only [stressMap_inner_symm,centeredContactGram]
  ring

theorem centeredSliceQMap_inner (q v : TangentCoordinates) (hq : q∈rotationSlice) (hv : v∈rotationSlice) :
    inner ℝ q (centeredSliceQMap v)=centeredContactGram q v := by
  rw [centeredSliceQMap,sliceProjection_eq_self _ hv,sliceProjection_inner _ _ hq,centeredQMap_inner]

theorem centered_quadratic_projected_identity :
    (∀q : TangentCoordinates,
      (∑e : ContactIndex,contactWeight e*‖sliceProjection (contactM e q-contactMeanM q)‖^2)=
      (∑e : ContactIndex,contactWeight e*‖sliceProjection (contactM e q)‖^2)-‖stressMap q‖^2/contactTotalWeight) ∧
    (∀v : TangentCoordinates,centeredQMap v=
      (∑e : ContactIndex,contactWeight e • contactM e (sliceProjection (contactM e v)))-
      contactTotalWeight⁻¹ • stressMap (stressMap v)) ∧
    (∀v : TangentCoordinates,centeredSliceQMap v=sliceProjection (centeredQMap (sliceProjection v))) ∧
    (∀q v : TangentCoordinates,inner ℝ q (centeredQMap v)=centeredContactGram q v) :=
  ⟨centered_quadratic_centered_norm_identity,fun _=>rfl,fun _=>rfl,centeredQMap_inner⟩

#print axioms centered_quadratic_projected_identity
end Blueprint.Thomson.Tail.Implementation
