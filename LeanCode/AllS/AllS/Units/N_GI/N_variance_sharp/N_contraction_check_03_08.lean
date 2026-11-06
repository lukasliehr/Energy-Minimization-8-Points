import AllS.Units.N_GI.N_variance_sharp.N_tensor_kernel_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceContraction_check_03_08 : ∀k : Fin 16,8≤k.val →
    varianceSymAUData 3 8 k=varianceCubicKernelData 3 8 k := by decide +kernel
#print axioms varianceContraction_check_03_08
end Blueprint.Thomson.Tail.Implementation
