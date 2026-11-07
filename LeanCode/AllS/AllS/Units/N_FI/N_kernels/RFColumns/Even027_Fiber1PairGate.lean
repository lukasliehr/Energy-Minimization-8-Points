import AllS.Units.N_FI.N_kernels.RFColumns.Even027_PairData
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even027.Fiber1PairGate
open Blueprint.Thomson.Finite.RFColumnProofs.Even027.PairData
theorem gate (j : Fin 3) : RFParityList.Gate false 1 j terms denominator (1,3,1) := by
  fin_cases j <;> unfold RFParityList.Gate RFParityList.Zero <;> decide +kernel
#print axioms gate
end Blueprint.Thomson.Finite.RFColumnProofs.Even027.Fiber1PairGate
