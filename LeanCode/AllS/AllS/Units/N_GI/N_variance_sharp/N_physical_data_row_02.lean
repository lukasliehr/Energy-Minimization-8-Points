import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceLinearData_exact_02 : ∀i,varianceLinearKernel (1,0) i=varianceLinearData 2 i := by decide +kernel
#print axioms varianceLinearData_exact_02
theorem varianceMData_exact_02 : ∀i j,varianceMKernel (1,0) i j=varianceMData 2 i j := by decide +kernel
#print axioms varianceMData_exact_02
theorem varianceProjectedLinearData_exact_02 : ∀i,varianceProjectedLinearFromData 2 i=varianceProjectedLinearData 2 i := by decide +kernel
#print axioms varianceProjectedLinearData_exact_02
theorem varianceProjectedMData_exact_02 : ∀i j,varianceProjectedMFromData 2 i j=varianceProjectedMData 2 i j := by decide +kernel
#print axioms varianceProjectedMData_exact_02
end Blueprint.Thomson.Tail.Implementation
