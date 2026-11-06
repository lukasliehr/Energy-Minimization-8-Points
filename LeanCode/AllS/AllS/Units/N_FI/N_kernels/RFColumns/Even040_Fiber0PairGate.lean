import AllS.Units.N_FI.N_kernels.RFColumns.Even040_PairData
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even040.Fiber0PairGate
open Blueprint.Thomson.Finite.RFColumnProofs.Even040.PairData
theorem gate (j : Fin 4) : RFParityList.Gate false 0 j terms denominator (0,5,1) := by
  fin_cases j <;> unfold RFParityList.Gate RFParityList.Zero <;> decide +kernel
#print axioms gate
end Blueprint.Thomson.Finite.RFColumnProofs.Even040.Fiber0PairGate
