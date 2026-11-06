import AllS.Units.N_FI.N_kernels.RFColumns.Even054_PairData
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even054.Fiber1PairGate
open Blueprint.Thomson.Finite.RFColumnProofs.Even054.PairData
theorem gate (j : Fin 3) : RFParityList.Gate false 1 j terms denominator (5,0,1) := by
  fin_cases j <;> unfold RFParityList.Gate RFParityList.Zero <;> decide +kernel
#print axioms gate
end Blueprint.Thomson.Finite.RFColumnProofs.Even054.Fiber1PairGate
