import AllS.Units.N_GI.N_variance_sharp.N_tensor_kernel_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceContraction_check_06_13 : ∀k : Fin 16,13≤k.val →
    varianceSymAUData 6 13 k=varianceCubicKernelData 6 13 k := by decide +kernel
#print axioms varianceContraction_check_06_13
end Blueprint.Thomson.Tail.Implementation
