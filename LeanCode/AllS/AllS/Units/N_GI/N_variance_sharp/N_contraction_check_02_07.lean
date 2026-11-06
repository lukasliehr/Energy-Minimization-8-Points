import AllS.Units.N_GI.N_variance_sharp.N_tensor_kernel_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceContraction_check_02_07 : ∀k : Fin 16,7≤k.val →
    varianceSymAUData 2 7 k=varianceCubicKernelData 2 7 k := by decide +kernel
#print axioms varianceContraction_check_02_07
end Blueprint.Thomson.Tail.Implementation
