import AllS.Units.N_GI.N_signed_mean.N_tensor_kernel_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation

theorem meanContraction_check_04_13 : ∀k : Fin 16, 13≤k.val →
    meanSymAUData 4 13 k=meanCubicKernelData 4 13 k := by decide +kernel

#print axioms meanContraction_check_04_13
end Blueprint.Thomson.Tail.Implementation
