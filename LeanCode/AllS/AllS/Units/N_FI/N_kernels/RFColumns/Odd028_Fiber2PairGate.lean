import AllS.Units.N_FI.N_kernels.RFColumns.Odd028_PairData
noncomputable section
open Blueprint.CAP Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd028.Fiber2PairGate
open Blueprint.Thomson.Finite.RFColumnProofs.Odd028.PairData
theorem gate (j : Fin 2) : RFParityList.Gate true 2 j terms denominator (0,6,0) := by
  fin_cases j <;> unfold RFParityList.Gate RFParityList.Zero <;> decide +kernel
#print axioms gate
end Blueprint.Thomson.Finite.RFColumnProofs.Odd028.Fiber2PairGate
