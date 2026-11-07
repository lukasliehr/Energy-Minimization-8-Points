import AllS.Units.N_GI.N_signed_mean.N_tensor_kernel_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation

theorem meanContraction_check_03_06 : ∀k : Fin 16, 6≤k.val →
    meanSymAUData 3 6 k=meanCubicKernelData 3 6 k := by decide +kernel

#print axioms meanContraction_check_03_06
end Blueprint.Thomson.Tail.Implementation
