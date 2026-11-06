import AllS.Units.N_FI.N_kernels.RFColumns.Odd033_PairData
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd033.Fiber3PairGate
open Blueprint.Thomson.Finite.RFColumnProofs.Odd033.PairData
theorem gate (j : Fin 1) : RFParityList.Gate true 3 j terms denominator (2,2,1) := by
  fin_cases j <;> unfold RFParityList.Gate RFParityList.Zero <;> decide +kernel
#print axioms gate
end Blueprint.Thomson.Finite.RFColumnProofs.Odd033.Fiber3PairGate
