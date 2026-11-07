import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceLinearData_exact_07 : ∀i,varianceLinearKernel (3,1) i=varianceLinearData 7 i := by decide +kernel
#print axioms varianceLinearData_exact_07
theorem varianceMData_exact_07 : ∀i j,varianceMKernel (3,1) i j=varianceMData 7 i j := by decide +kernel
#print axioms varianceMData_exact_07
theorem varianceProjectedLinearData_exact_07 : ∀i,varianceProjectedLinearFromData 7 i=varianceProjectedLinearData 7 i := by decide +kernel
#print axioms varianceProjectedLinearData_exact_07
theorem varianceProjectedMData_exact_07 : ∀i j,varianceProjectedMFromData 7 i j=varianceProjectedMData 7 i j := by decide +kernel
#print axioms varianceProjectedMData_exact_07
end Blueprint.Thomson.Tail.Implementation
