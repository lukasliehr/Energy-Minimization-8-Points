import AllS.Units.N_GI.N_variance_sharp.N_rotation_kernels
import AllS.Units.N_GI.N_variance_sharp.N_tensor_coordinates
import AllS.Units.N_GI.N_signed_mean.N_tensor_symmetrization

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem varianceProjectedBasis_synthesis (q : TangentCoordinates) :
    (∑i : Fin 16,meanFlatBasis.repr q i • sliceProjection (meanFlatBasis i))=sliceProjection q := by
  let P : TangentCoordinates →ₗ[ℝ] TangentCoordinates := LinearMap.id-varianceRotationOperator
  have hp (q : TangentCoordinates) : P q=sliceProjection q := rfl
  simp_rw [← hp,← map_smul]
  rw [← map_sum]
  have hq : (∑i : Fin 16,meanFlatBasis.repr q i • meanFlatBasis i)=q := by
    simpa only [OrthonormalBasis.repr_apply_apply] using meanFlatBasis.sum_repr' q
  rw [hq]

theorem varianceProjectedTensor_contraction (q : TangentCoordinates) :
    tensorCubic (fun i j k=>varianceTrilinear (sliceProjection (meanFlatBasis i))
      (sliceProjection (meanFlatBasis j)) (sliceProjection (meanFlatBasis k)))
      (meanFlatBasis.repr q)=varianceCubic (sliceProjection q) := by
  rw [← varianceProjectedBasis_synthesis q]
  rw [varianceTrilinear_synthesis]
  unfold tensorCubic
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

#print axioms varianceProjectedTensor_contraction
end Blueprint.Thomson.Tail.Implementation
