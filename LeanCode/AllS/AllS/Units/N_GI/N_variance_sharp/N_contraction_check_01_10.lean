import AllS.Units.N_GI.N_variance_sharp.N_tensor_kernel_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceContraction_check_01_10 : ∀k : Fin 16,10≤k.val →
    varianceSymAUData 1 10 k=varianceCubicKernelData 1 10 k := by decide +kernel
#print axioms varianceContraction_check_01_10
end Blueprint.Thomson.Tail.Implementation
