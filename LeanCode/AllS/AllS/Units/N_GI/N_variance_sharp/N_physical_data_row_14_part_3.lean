import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceProjectedMData_exact_14 : ∀i j,varianceProjectedMFromData 14 i j=varianceProjectedMData 14 i j := by decide +kernel
#print axioms varianceProjectedMData_exact_14

end Blueprint.Thomson.Tail.Implementation
