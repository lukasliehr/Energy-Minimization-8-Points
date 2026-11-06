import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceProjectedLinearData_exact_15 : ∀i,varianceProjectedLinearFromData 15 i=varianceProjectedLinearData 15 i := by decide +kernel
#print axioms varianceProjectedLinearData_exact_15
end Blueprint.Thomson.Tail.Implementation
