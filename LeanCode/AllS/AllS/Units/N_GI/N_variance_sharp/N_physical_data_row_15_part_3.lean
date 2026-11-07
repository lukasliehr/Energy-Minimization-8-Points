import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceProjectedMData_exact_15 : ∀i j,varianceProjectedMFromData 15 i j=varianceProjectedMData 15 i j := by decide +kernel
#print axioms varianceProjectedMData_exact_15

end Blueprint.Thomson.Tail.Implementation
