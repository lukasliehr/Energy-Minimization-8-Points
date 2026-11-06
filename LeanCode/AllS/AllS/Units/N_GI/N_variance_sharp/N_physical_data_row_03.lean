import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceLinearData_exact_03 : ∀i,varianceLinearKernel (1,1) i=varianceLinearData 3 i := by decide +kernel
#print axioms varianceLinearData_exact_03
theorem varianceMData_exact_03 : ∀i j,varianceMKernel (1,1) i j=varianceMData 3 i j := by decide +kernel
#print axioms varianceMData_exact_03
theorem varianceProjectedLinearData_exact_03 : ∀i,varianceProjectedLinearFromData 3 i=varianceProjectedLinearData 3 i := by decide +kernel
#print axioms varianceProjectedLinearData_exact_03
theorem varianceProjectedMData_exact_03 : ∀i j,varianceProjectedMFromData 3 i j=varianceProjectedMData 3 i j := by decide +kernel
#print axioms varianceProjectedMData_exact_03
end Blueprint.Thomson.Tail.Implementation
