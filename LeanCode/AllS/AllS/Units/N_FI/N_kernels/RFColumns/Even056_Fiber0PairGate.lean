import AllS.Units.N_FI.N_kernels.RFColumns.Even056_PairData
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even056.Fiber0PairGate
open Blueprint.Thomson.Finite.RFColumnProofs.Even056.PairData
theorem gate (j : Fin 4) : RFParityList.Gate false 0 j terms denominator (6,1,0) := by
  fin_cases j <;> unfold RFParityList.Gate RFParityList.Zero <;> decide +kernel
#print axioms gate
end Blueprint.Thomson.Finite.RFColumnProofs.Even056.Fiber0PairGate
