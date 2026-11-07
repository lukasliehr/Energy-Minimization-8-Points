import AllS.Units.N_FI.N_kernels.RFColumns.Odd047_PairData
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd047.Fiber1PairGate
open Blueprint.Thomson.Finite.RFColumnProofs.Odd047.PairData
theorem gate (j : Fin 3) : RFParityList.Gate true 1 j terms denominator (1,4,1) := by
  fin_cases j <;> unfold RFParityList.Gate RFParityList.Zero <;> decide +kernel
#print axioms gate
end Blueprint.Thomson.Finite.RFColumnProofs.Odd047.Fiber1PairGate
