import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceLinearData_exact_14 : ∀i,varianceLinearKernel (7,0) i=varianceLinearData 14 i := by decide +kernel
#print axioms varianceLinearData_exact_14
end Blueprint.Thomson.Tail.Implementation
