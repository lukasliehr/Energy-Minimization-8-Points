import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceLinearData_exact_05 : ∀i,varianceLinearKernel (2,1) i=varianceLinearData 5 i := by decide +kernel
#print axioms varianceLinearData_exact_05
theorem varianceMData_exact_05 : ∀i j,varianceMKernel (2,1) i j=varianceMData 5 i j := by decide +kernel
#print axioms varianceMData_exact_05
theorem varianceProjectedLinearData_exact_05 : ∀i,varianceProjectedLinearFromData 5 i=varianceProjectedLinearData 5 i := by decide +kernel
#print axioms varianceProjectedLinearData_exact_05
theorem varianceProjectedMData_exact_05 : ∀i j,varianceProjectedMFromData 5 i j=varianceProjectedMData 5 i j := by decide +kernel
#print axioms varianceProjectedMData_exact_05
end Blueprint.Thomson.Tail.Implementation
