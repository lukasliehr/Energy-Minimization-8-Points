import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceProjectedLinearData_exact_12 : ∀i,varianceProjectedLinearFromData 12 i=varianceProjectedLinearData 12 i := by decide +kernel
#print axioms varianceProjectedLinearData_exact_12
end Blueprint.Thomson.Tail.Implementation
