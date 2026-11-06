import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceLinearData_exact_00 : ∀i,varianceLinearKernel (0,0) i=varianceLinearData 0 i := by decide +kernel
#print axioms varianceLinearData_exact_00
theorem varianceMData_exact_00 : ∀i j,varianceMKernel (0,0) i j=varianceMData 0 i j := by decide +kernel
#print axioms varianceMData_exact_00
theorem varianceProjectedLinearData_exact_00 : ∀i,varianceProjectedLinearFromData 0 i=varianceProjectedLinearData 0 i := by decide +kernel
#print axioms varianceProjectedLinearData_exact_00
theorem varianceProjectedMData_exact_00 : ∀i j,varianceProjectedMFromData 0 i j=varianceProjectedMData 0 i j := by decide +kernel
#print axioms varianceProjectedMData_exact_00
end Blueprint.Thomson.Tail.Implementation
