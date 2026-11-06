import AllS.Units.N_GI.N_variance_sharp.N_tensor_kernel_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceContraction_check_05_05 : ∀k : Fin 16,5≤k.val →
    varianceSymAUData 5 5 k=varianceCubicKernelData 5 5 k := by decide +kernel
#print axioms varianceContraction_check_05_05
end Blueprint.Thomson.Tail.Implementation
