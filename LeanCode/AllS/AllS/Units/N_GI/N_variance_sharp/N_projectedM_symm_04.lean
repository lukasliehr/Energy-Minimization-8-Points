import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceProjectedMData_symm_04 : ∀i j,
    varianceProjectedMData 4 i j=varianceProjectedMData 4 j i := by decide +kernel
#print axioms varianceProjectedMData_symm_04
end Blueprint.Thomson.Tail.Implementation
