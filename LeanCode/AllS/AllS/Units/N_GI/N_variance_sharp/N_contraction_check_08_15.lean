import AllS.Units.N_GI.N_variance_sharp.N_tensor_kernel_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceContraction_check_08_15 : ∀k : Fin 16,15≤k.val →
    varianceSymAUData 8 15 k=varianceCubicKernelData 8 15 k := by decide +kernel
#print axioms varianceContraction_check_08_15
end Blueprint.Thomson.Tail.Implementation
