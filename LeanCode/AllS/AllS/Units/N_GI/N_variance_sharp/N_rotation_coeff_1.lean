import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceRotationCoeffData_exact_1 : ∀i,
    varianceRotationCoeffKernel 1 i=varianceRotationCoeffData 1 i := by decide +kernel
#print axioms varianceRotationCoeffData_exact_1
end Blueprint.Thomson.Tail.Implementation
