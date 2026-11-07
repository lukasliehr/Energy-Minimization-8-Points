import AllS.Units.N_GI.N_signed_mean.N_tensor_kernel_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation

theorem meanContraction_check_02_07 : ∀k : Fin 16, 7≤k.val →
    meanSymAUData 2 7 k=meanCubicKernelData 2 7 k := by decide +kernel

#print axioms meanContraction_check_02_07
end Blueprint.Thomson.Tail.Implementation
