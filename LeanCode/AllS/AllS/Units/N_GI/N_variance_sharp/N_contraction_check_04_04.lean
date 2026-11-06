import AllS.Units.N_GI.N_variance_sharp.N_tensor_kernel_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceContraction_check_04_04 : ∀k : Fin 16,4≤k.val →
    varianceSymAUData 4 4 k=varianceCubicKernelData 4 4 k := by decide +kernel
#print axioms varianceContraction_check_04_04
end Blueprint.Thomson.Tail.Implementation
