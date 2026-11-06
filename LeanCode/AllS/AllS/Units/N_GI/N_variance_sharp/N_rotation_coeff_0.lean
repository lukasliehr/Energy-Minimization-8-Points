import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceRotationCoeffData_exact_0 : ∀i,
    varianceRotationCoeffKernel 0 i=varianceRotationCoeffData 0 i := by decide +kernel
#print axioms varianceRotationCoeffData_exact_0
end Blueprint.Thomson.Tail.Implementation
