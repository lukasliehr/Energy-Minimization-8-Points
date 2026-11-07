import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceRotationCoeffData_exact_2 : ∀i,
    varianceRotationCoeffKernel 2 i=varianceRotationCoeffData 2 i := by decide +kernel
#print axioms varianceRotationCoeffData_exact_2
end Blueprint.Thomson.Tail.Implementation
