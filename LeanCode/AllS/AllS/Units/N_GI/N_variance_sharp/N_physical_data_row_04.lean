import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceLinearData_exact_04 : ∀i,varianceLinearKernel (2,0) i=varianceLinearData 4 i := by decide +kernel
#print axioms varianceLinearData_exact_04
theorem varianceMData_exact_04 : ∀i j,varianceMKernel (2,0) i j=varianceMData 4 i j := by decide +kernel
#print axioms varianceMData_exact_04
theorem varianceProjectedLinearData_exact_04 : ∀i,varianceProjectedLinearFromData 4 i=varianceProjectedLinearData 4 i := by decide +kernel
#print axioms varianceProjectedLinearData_exact_04
theorem varianceProjectedMData_exact_04 : ∀i j,varianceProjectedMFromData 4 i j=varianceProjectedMData 4 i j := by decide +kernel
#print axioms varianceProjectedMData_exact_04
end Blueprint.Thomson.Tail.Implementation
