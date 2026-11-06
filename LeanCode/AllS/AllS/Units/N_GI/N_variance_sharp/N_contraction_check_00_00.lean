import AllS.Units.N_GI.N_variance_sharp.N_tensor_kernel_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceContraction_check_00_00 : ∀k : Fin 16,0≤k.val →
    varianceSymAUData 0 0 k=varianceCubicKernelData 0 0 k := by decide +kernel
#print axioms varianceContraction_check_00_00
end Blueprint.Thomson.Tail.Implementation
