import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceProjectedLinearData_exact_13 : ∀i,varianceProjectedLinearFromData 13 i=varianceProjectedLinearData 13 i := by decide +kernel
#print axioms varianceProjectedLinearData_exact_13
end Blueprint.Thomson.Tail.Implementation
