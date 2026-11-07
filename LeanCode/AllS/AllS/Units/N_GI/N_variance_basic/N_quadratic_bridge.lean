import AllS.Units.N_GI.N_centered_quadratic.N_projected_identity
import AllS.Units.N_GI.N_variance_basic.N_lower_helpers

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem contactMeanM_quadratic (q : TangentCoordinates) :
    inner ℝ q (contactMeanM q)=contactMean (contactQuadraticArray q) := by
  simp only [contactMeanM,real_inner_smul_right,stressMap,inner_sum,real_inner_smul_right,
    contactM_quadratic,contactMean,contactQuadraticArray,div_eq_mul_inv]
  ring

theorem centered_contactM_quadratic (q : TangentCoordinates) (hq : q∈rotationSlice) (e : ContactIndex) :
    inner ℝ q (sliceProjection (contactM e q-contactMeanM q))=contactCenter (contactQuadraticArray q) e := by
  rw [sliceProjection_inner q _ hq,inner_sub_right,contactM_quadratic,contactMeanM_quadratic]
  rfl

theorem variance_quadratic_norm_of_projected_bound (q : TangentCoordinates) (hq : q∈rotationSlice)
    (hQ : (∑ e : ContactIndex,contactWeight e*‖sliceProjection (contactM e q-contactMeanM q)‖^2)≤4*‖q‖^2) :
    contactNorm (contactCenter (contactQuadraticArray q))≤2*‖q‖^2 := by
  have hpoint (e : ContactIndex) : (contactCenter (contactQuadraticArray q) e)^2≤
      ‖q‖^2*‖sliceProjection (contactM e q-contactMeanM q)‖^2 := by
    have h := real_inner_mul_inner_self_le q (sliceProjection (contactM e q-contactMeanM q))
    simpa only [centered_contactM_quadratic q hq e,real_inner_self_eq_norm_sq,←sq] using h
  have hsum : (contactNorm (contactCenter (contactQuadraticArray q)))^2≤
      ‖q‖^2*(∑ e : ContactIndex,contactWeight e*‖sliceProjection (contactM e q-contactMeanM q)‖^2) := by
    rw [contactNorm_sq,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    have h := mul_le_mul_of_nonneg_left (hpoint e) (contactWeight_pos e).le
    convert! h using 1 <;> ring
  have hh := mul_le_mul_of_nonneg_left hQ (sq_nonneg ‖q‖)
  nlinarith [contactNorm_nonneg (contactCenter (contactQuadraticArray q))]

#print axioms variance_quadratic_norm_of_projected_bound
end Blueprint.Thomson.Tail.Implementation
