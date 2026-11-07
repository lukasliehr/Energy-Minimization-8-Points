import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceLinearData_exact_06 : ∀i,varianceLinearKernel (3,0) i=varianceLinearData 6 i := by decide +kernel
#print axioms varianceLinearData_exact_06
theorem varianceMData_exact_06 : ∀i j,varianceMKernel (3,0) i j=varianceMData 6 i j := by decide +kernel
#print axioms varianceMData_exact_06
theorem varianceProjectedLinearData_exact_06 : ∀i,varianceProjectedLinearFromData 6 i=varianceProjectedLinearData 6 i := by decide +kernel
#print axioms varianceProjectedLinearData_exact_06
theorem varianceProjectedMData_exact_06 : ∀i j,varianceProjectedMFromData 6 i j=varianceProjectedMData 6 i j := by decide +kernel
#print axioms varianceProjectedMData_exact_06
end Blueprint.Thomson.Tail.Implementation
