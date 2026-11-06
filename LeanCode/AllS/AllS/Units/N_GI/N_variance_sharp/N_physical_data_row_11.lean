import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceLinearData_exact_11 : ∀i,varianceLinearKernel (5,1) i=varianceLinearData 11 i := by decide +kernel
#print axioms varianceLinearData_exact_11
theorem varianceMData_exact_11 : ∀i j,varianceMKernel (5,1) i j=varianceMData 11 i j := by decide +kernel
#print axioms varianceMData_exact_11
theorem varianceProjectedLinearData_exact_11 : ∀i,varianceProjectedLinearFromData 11 i=varianceProjectedLinearData 11 i := by decide +kernel
#print axioms varianceProjectedLinearData_exact_11
theorem varianceProjectedMData_exact_11 : ∀i j,varianceProjectedMFromData 11 i j=varianceProjectedMData 11 i j := by decide +kernel
#print axioms varianceProjectedMData_exact_11
end Blueprint.Thomson.Tail.Implementation
