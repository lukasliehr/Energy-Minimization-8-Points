import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceProjectedMData_exact_12 : ∀i j,varianceProjectedMFromData 12 i j=varianceProjectedMData 12 i j := by decide +kernel
#print axioms varianceProjectedMData_exact_12

end Blueprint.Thomson.Tail.Implementation
