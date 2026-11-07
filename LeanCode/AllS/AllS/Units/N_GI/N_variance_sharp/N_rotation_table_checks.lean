import AllS.Units.N_GI.N_variance_sharp.N_physical_data
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
namespace Blueprint.Thomson.Tail.Implementation
theorem varianceRotationFromCoeff_exact : ∀i j,varianceRotationFromCoeff i j=varianceRotationProjectionData i j := by decide +kernel
theorem varianceSliceProjectionData_exact : ∀i j,
    varianceSliceProjectionData i j=(if i=j then ![1,0,0,0] else 0)-varianceRotationProjectionData i j := by decide +kernel
theorem varianceSliceProjectionData_block : ∀i j,
    ((finProdFinEquiv (m:=8) (n:=2)).symm i).1≠((finProdFinEquiv (m:=8) (n:=2)).symm j).1 →
    varianceSliceProjectionData i j=0 := by decide +kernel
#print axioms varianceRotationFromCoeff_exact
#print axioms varianceSliceProjectionData_block
end Blueprint.Thomson.Tail.Implementation
