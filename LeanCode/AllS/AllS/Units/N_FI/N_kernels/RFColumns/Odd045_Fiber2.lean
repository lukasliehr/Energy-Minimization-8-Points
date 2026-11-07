import AllS.Units.N_FI.N_kernels.RFColumns.Odd045_Fiber2PairGate
import AllS.Units.N_FI.N_kernels.RFColumns.Odd045_Vector
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2
import AllS.Generated.FiniteKernelRFCatalogue.Chunk3

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd045
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem values2 (a : ℝ) (ha : physical a) (h0 : rf1929.DefinedAt a) (h1 : rf1948.DefinedAt a) (h2 : rf1985.DefinedAt a) (h3 : rf1966.DefinedAt a) (h4 : rf2003.DefinedAt a) (h5 : rf2040.DefinedAt a) (h6 : rf2021.DefinedAt a) (h7 : rf2058.DefinedAt a) (h8 : rf2076.DefinedAt a) :
    ∀ j : Fin (parityFiberSize true 2),(∑ r,vector a r*(parityFiberU a true 2)^r.1.val*(parityFiberZ a true 2 j)^r.2.val)=paritySourceData a true (1,0,3) 2 j := by
  intro j
  have ha0 : a≠0 := by
    have hlo := lt_trans packing_endpoint_bounds.1 ha.1
    linarith
  have hD : evalQPoly den a≠0 := h0
  have hcheck:=RFParityList.checked_identity true 2 j Blueprint.Thomson.Finite.RFColumnProofs.Odd045.PairData.terms Blueprint.Thomson.Finite.RFColumnProofs.Odd045.PairData.denominator (1,0,3) (Blueprint.Thomson.Finite.RFColumnProofs.Odd045.Fiber2PairGate.gate j) a
  simp only [Blueprint.Thomson.Finite.RFColumnProofs.Odd045.PairData.terms,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hcheck
  simp only [Blueprint.Thomson.Finite.RFColumnProofs.Odd045.PairData.num000_eval,Blueprint.Thomson.Finite.RFColumnProofs.Odd045.PairData.num001_eval,Blueprint.Thomson.Finite.RFColumnProofs.Odd045.PairData.num002_eval,Blueprint.Thomson.Finite.RFColumnProofs.Odd045.PairData.num003_eval,Blueprint.Thomson.Finite.RFColumnProofs.Odd045.PairData.num004_eval,Blueprint.Thomson.Finite.RFColumnProofs.Odd045.PairData.num005_eval,Blueprint.Thomson.Finite.RFColumnProofs.Odd045.PairData.num006_eval,Blueprint.Thomson.Finite.RFColumnProofs.Odd045.PairData.num007_eval,Blueprint.Thomson.Finite.RFColumnProofs.Odd045.PairData.num008_eval,Blueprint.Thomson.Finite.RFColumnProofs.Odd045.PairData.denominator_eval] at hcheck
  rw [parity_sum_odd]
  norm_num [vector,eval0 a h0 hD,eval1 a h1 hD,eval2 a h2 hD,eval3 a h3 hD,eval4 a h4 hD,eval5 a h5 hD,eval6 a h6 hD,eval7 a h7 hD,eval8 a h8 hD]
  field_simp [hD]
  linear_combination hcheck

#print axioms values2

end Blueprint.Thomson.Finite.RFColumnProofs.Odd045
