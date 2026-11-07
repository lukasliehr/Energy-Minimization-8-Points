import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceLinearData_exact_01 : ∀i,varianceLinearKernel (0,1) i=varianceLinearData 1 i := by decide +kernel
#print axioms varianceLinearData_exact_01
theorem varianceMData_exact_01 : ∀i j,varianceMKernel (0,1) i j=varianceMData 1 i j := by decide +kernel
#print axioms varianceMData_exact_01
theorem varianceProjectedLinearData_exact_01 : ∀i,varianceProjectedLinearFromData 1 i=varianceProjectedLinearData 1 i := by decide +kernel
#print axioms varianceProjectedLinearData_exact_01
theorem varianceProjectedMData_exact_01 : ∀i j,varianceProjectedMFromData 1 i j=varianceProjectedMData 1 i j := by decide +kernel
#print axioms varianceProjectedMData_exact_01
end Blueprint.Thomson.Tail.Implementation
