import AllS.Units.N_GI.N_variance_sharp.N_tensor_kernel_data
import AllS.Units.N_GI.N_variance_sharp.N_rotation_data_exact
import AllS.Units.N_GI.N_signed_mean.N_tensor_symmetry

noncomputable section
namespace Blueprint.Thomson.Tail.Implementation

theorem varianceCubicKernelData_swap12 (i j k : Fin 16) :
    varianceCubicKernelData i j k=varianceCubicKernelData j i k := by
  unfold varianceCubicKernelData
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [varianceProjectedMData_symm (finProdFinEquiv e) i j]
  congr 1
  abel

theorem varianceCubicKernelData_swap23 (i j k : Fin 16) :
    varianceCubicKernelData i j k=varianceCubicKernelData i k j := by
  unfold varianceCubicKernelData
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [varianceProjectedMData_symm (finProdFinEquiv e) j k]
  congr 1
  abel

theorem varianceSymAUData_swap12 (i j k : Fin 16) : varianceSymAUData i j k=varianceSymAUData j i k := by
  unfold varianceSymAUData
  congr 1
  abel

theorem varianceSymAUData_swap23 (i j k : Fin 16) : varianceSymAUData i j k=varianceSymAUData i k j := by
  unfold varianceSymAUData
  congr 1
  abel

#print axioms varianceCubicKernelData_swap12
#print axioms varianceCubicKernelData_swap23
end Blueprint.Thomson.Tail.Implementation
