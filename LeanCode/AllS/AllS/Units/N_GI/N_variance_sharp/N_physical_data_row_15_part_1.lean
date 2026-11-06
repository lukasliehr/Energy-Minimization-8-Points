import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceMData_exact_15 : ∀i j,varianceMKernel (7,1) i j=varianceMData 15 i j := by decide +kernel
#print axioms varianceMData_exact_15
end Blueprint.Thomson.Tail.Implementation
