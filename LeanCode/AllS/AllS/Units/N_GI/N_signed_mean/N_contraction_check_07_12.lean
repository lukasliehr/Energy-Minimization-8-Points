import AllS.Units.N_GI.N_signed_mean.N_tensor_kernel_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation

theorem meanContraction_check_07_12 : ∀k : Fin 16, 12≤k.val →
    meanSymAUData 7 12 k=meanCubicKernelData 7 12 k := by decide +kernel

#print axioms meanContraction_check_07_12
end Blueprint.Thomson.Tail.Implementation
