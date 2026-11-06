import AllS.Units.N_GI.N_signed_mean.N_physical_bounds
import AllS.Units.N_GI.N_centered_quadratic.N_contact_operator

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

def stressLinearMap : TangentCoordinates →ₗ[ℝ] TangentCoordinates where
  toFun := stressMap
  map_add' q v := by simp [stressMap,contactM_add,smul_add,Finset.sum_add_distrib]
  map_smul' c q := by
    simp [stressMap,contactM_smul,Finset.smul_sum,smul_smul,mul_comm]

def meanAbsorptionOperator : TangentCoordinates →ₗ[ℝ] TangentCoordinates :=
  (829/200:ℝ) • LinearMap.id-stressLinearMap

theorem meanAbsorptionOperator_inner (q v : TangentCoordinates) :
    inner ℝ q (meanAbsorptionOperator v)=(829:ℝ)/200*inner ℝ q v-stressH q v := by
  change inner ℝ q (((829:ℝ)/200) • v-stressMap v)=_
  rw [inner_sub_right,real_inner_smul_right,stressMap_inner]

theorem meanAbsorptionOperator_symmetric : meanAbsorptionOperator.IsSymmetric := by
  intro q v
  rw [real_inner_comm,meanAbsorptionOperator_inner,meanAbsorptionOperator_inner,stressH_symm,
    real_inner_comm q v]

theorem meanAbsorptionOperator_positive (q : TangentCoordinates) (hq : q≠0) :
    0 < inner ℝ q (meanAbsorptionOperator q) := by
  rw [meanAbsorptionOperator_inner,real_inner_self_eq_norm_sq]
  have hs := stressH_strict_upper q hq
  have hn := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hq)
  nlinarith

theorem meanAbsorptionOperator_nonnegative (q : TangentCoordinates) :
    0 ≤ inner ℝ q (meanAbsorptionOperator q) := by
  by_cases hq : q=0
  · simp [hq]
  · exact (meanAbsorptionOperator_positive q hq).le

#print axioms meanAbsorptionOperator_symmetric
#print axioms meanAbsorptionOperator_positive
end Blueprint.Thomson.Tail.Implementation
