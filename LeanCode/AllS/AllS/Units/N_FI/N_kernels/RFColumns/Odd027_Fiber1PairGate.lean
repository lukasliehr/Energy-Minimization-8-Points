import AllS.Units.N_FI.N_kernels.RFColumns.Odd027_PairData
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd027.Fiber1PairGate
open Blueprint.Thomson.Finite.RFColumnProofs.Odd027.PairData
theorem gate (j : Fin 3) : RFParityList.Gate true 1 j terms denominator (0,4,1) := by
  fin_cases j <;> unfold RFParityList.Gate RFParityList.Zero <;> decide +kernel
#print axioms gate
end Blueprint.Thomson.Finite.RFColumnProofs.Odd027.Fiber1PairGate
