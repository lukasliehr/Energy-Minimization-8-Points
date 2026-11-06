import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceLinearData_exact_09 : ∀i,varianceLinearKernel (4,1) i=varianceLinearData 9 i := by decide +kernel
#print axioms varianceLinearData_exact_09
theorem varianceMData_exact_09 : ∀i j,varianceMKernel (4,1) i j=varianceMData 9 i j := by decide +kernel
#print axioms varianceMData_exact_09
theorem varianceProjectedLinearData_exact_09 : ∀i,varianceProjectedLinearFromData 9 i=varianceProjectedLinearData 9 i := by decide +kernel
#print axioms varianceProjectedLinearData_exact_09
theorem varianceProjectedMData_exact_09 : ∀i j,varianceProjectedMFromData 9 i j=varianceProjectedMData 9 i j := by decide +kernel
#print axioms varianceProjectedMData_exact_09
end Blueprint.Thomson.Tail.Implementation
