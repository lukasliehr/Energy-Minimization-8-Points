import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceLinearData_exact_10 : ∀i,varianceLinearKernel (5,0) i=varianceLinearData 10 i := by decide +kernel
#print axioms varianceLinearData_exact_10
theorem varianceMData_exact_10 : ∀i j,varianceMKernel (5,0) i j=varianceMData 10 i j := by decide +kernel
#print axioms varianceMData_exact_10
theorem varianceProjectedLinearData_exact_10 : ∀i,varianceProjectedLinearFromData 10 i=varianceProjectedLinearData 10 i := by decide +kernel
#print axioms varianceProjectedLinearData_exact_10
theorem varianceProjectedMData_exact_10 : ∀i j,varianceProjectedMFromData 10 i j=varianceProjectedMData 10 i j := by decide +kernel
#print axioms varianceProjectedMData_exact_10
end Blueprint.Thomson.Tail.Implementation
