import AllS.Units.N_FI.N_kernels.RFColumns.Odd015_PairData
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd015.Fiber3PairGate
open Blueprint.Thomson.Finite.RFColumnProofs.Odd015.PairData
theorem gate (j : Fin 1) : RFParityList.Gate true 3 j terms denominator (0,5,0) := by
  fin_cases j <;> unfold RFParityList.Gate RFParityList.Zero <;> decide +kernel
#print axioms gate
end Blueprint.Thomson.Finite.RFColumnProofs.Odd015.Fiber3PairGate
