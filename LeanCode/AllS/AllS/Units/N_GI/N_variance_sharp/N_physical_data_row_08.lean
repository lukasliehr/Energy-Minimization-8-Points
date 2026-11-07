import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceLinearData_exact_08 : ∀i,varianceLinearKernel (4,0) i=varianceLinearData 8 i := by decide +kernel
#print axioms varianceLinearData_exact_08
theorem varianceMData_exact_08 : ∀i j,varianceMKernel (4,0) i j=varianceMData 8 i j := by decide +kernel
#print axioms varianceMData_exact_08
theorem varianceProjectedLinearData_exact_08 : ∀i,varianceProjectedLinearFromData 8 i=varianceProjectedLinearData 8 i := by decide +kernel
#print axioms varianceProjectedLinearData_exact_08
theorem varianceProjectedMData_exact_08 : ∀i j,varianceProjectedMFromData 8 i j=varianceProjectedMData 8 i j := by decide +kernel
#print axioms varianceProjectedMData_exact_08
end Blueprint.Thomson.Tail.Implementation
