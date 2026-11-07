import AllS.Units.N_GI.N_signed_mean.N_tensor_kernel_data
import AllS.Units.N_GI.N_signed_mean.N_basis_coefficients
import AllS.Units.N_GI.N_signed_mean.N_cubic_tensor

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem meanOrderedCubic_kernel (i j k : Fin 16) :
    meanOrderedCubic (meanFlatBasis i) (meanFlatBasis j) (meanFlatBasis k)=
      packingRadius*meanRadicalEval (meanOrderedKernelData i j k) := by
  unfold meanOrderedCubic
  rw [meanFlatBasis_apply i,stressB_vertex_kernel]
  simp only [tangentVector_self_inner,meanFlatBasis_coordinates,meanBVertexKernel_data]
  simp only [meanOrderedKernelData,meanRadicalEval_neg,meanRadicalEval_sum,
    meanRadicalEval_mul,meanDotKernelData,meanRadicalEval_add]
  ring

theorem meanPhysicalTensor_kernel (i j k : Fin 16) :
    meanPhysicalTensor meanFlatBasis i j k=packingRadius*meanRadicalEval (meanCubicKernelData i j k) := by
  simp only [meanPhysicalTensor,meanOrderedCubic_kernel,meanCubicKernelData,
    meanRadicalEval_smul,meanRadicalEval_add]
  norm_num
  ring

#print axioms meanPhysicalTensor_kernel
end Blueprint.Thomson.Tail.Implementation
