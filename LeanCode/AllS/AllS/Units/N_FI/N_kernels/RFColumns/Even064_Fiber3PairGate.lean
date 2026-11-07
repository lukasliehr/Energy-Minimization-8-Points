import AllS.Units.N_FI.N_kernels.RFColumns.Even064_PairData
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even064.Fiber3PairGate
open Blueprint.Thomson.Finite.RFColumnProofs.Even064.PairData
theorem gate (j : Fin 2) : RFParityList.Gate false 3 j terms denominator (1,3,2) := by
  fin_cases j <;> unfold RFParityList.Gate RFParityList.Zero <;> decide +kernel
#print axioms gate
end Blueprint.Thomson.Finite.RFColumnProofs.Even064.Fiber3PairGate
