import AllS.Units.N_GI.N_signed_mean.N_tensor_kernel_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation

theorem meanContraction_check_14_14 : ∀k : Fin 16, 14≤k.val →
    meanSymAUData 14 14 k=meanCubicKernelData 14 14 k := by decide +kernel

#print axioms meanContraction_check_14_14
end Blueprint.Thomson.Tail.Implementation
