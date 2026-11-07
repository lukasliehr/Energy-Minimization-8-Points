import AllS.Units.N_GI.N_signed_mean.N_tensor_kernel_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation

theorem meanContraction_check_02_04 : ∀k : Fin 16, 4≤k.val →
    meanSymAUData 2 4 k=meanCubicKernelData 2 4 k := by decide +kernel

#print axioms meanContraction_check_02_04
end Blueprint.Thomson.Tail.Implementation
