import AllS.Units.N_FI.N_kernels.RFColumns.Odd060_Fiber1PairGate
import AllS.Units.N_FI.N_kernels.RFColumns.Odd060_Vector
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk2

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Odd060
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem values1 (a : ℝ) (ha : physical a) (h0 : rf1327.DefinedAt a) (h1 : rf0013.DefinedAt a) (h2 : rf0013.DefinedAt a) (h3 : rf1363.DefinedAt a) (h4 : rf0013.DefinedAt a) (h5 : rf0013.DefinedAt a) (h6 : rf1417.DefinedAt a) (h7 : rf0013.DefinedAt a) (h8 : rf1488.DefinedAt a) :
    ∀ j : Fin (parityFiberSize true 1),(∑ r,vector a r*(parityFiberU a true 1)^r.1.val*(parityFiberZ a true 1 j)^r.2.val)=paritySourceData a true (7,0,0) 1 j := by
  intro j
  have ha0 : a≠0 := by
    have hlo := lt_trans packing_endpoint_bounds.1 ha.1
    linarith
  have hD : evalQPoly den a≠0 := h0
  have hcheck:=RFParityList.checked_identity true 1 j Blueprint.Thomson.Finite.RFColumnProofs.Odd060.PairData.terms Blueprint.Thomson.Finite.RFColumnProofs.Odd060.PairData.denominator (7,0,0) (Blueprint.Thomson.Finite.RFColumnProofs.Odd060.Fiber1PairGate.gate j) a
  simp only [Blueprint.Thomson.Finite.RFColumnProofs.Odd060.PairData.terms,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hcheck
  simp only [Blueprint.Thomson.Finite.RFColumnProofs.Odd060.PairData.num000_eval,Blueprint.Thomson.Finite.RFColumnProofs.Odd060.PairData.num001_eval,Blueprint.Thomson.Finite.RFColumnProofs.Odd060.PairData.num002_eval,Blueprint.Thomson.Finite.RFColumnProofs.Odd060.PairData.num003_eval,Blueprint.Thomson.Finite.RFColumnProofs.Odd060.PairData.num004_eval,Blueprint.Thomson.Finite.RFColumnProofs.Odd060.PairData.num005_eval,Blueprint.Thomson.Finite.RFColumnProofs.Odd060.PairData.num006_eval,Blueprint.Thomson.Finite.RFColumnProofs.Odd060.PairData.num007_eval,Blueprint.Thomson.Finite.RFColumnProofs.Odd060.PairData.num008_eval,Blueprint.Thomson.Finite.RFColumnProofs.Odd060.PairData.denominator_eval] at hcheck
  rw [parity_sum_odd]
  norm_num [vector,eval0 a h0 hD,eval1 a h1 hD,eval2 a h2 hD,eval3 a h3 hD,eval4 a h4 hD,eval5 a h5 hD,eval6 a h6 hD,eval7 a h7 hD,eval8 a h8 hD]
  have h_alias2 : n2=n1 := rfl
  have h_alias4 : n4=n1 := rfl
  have h_alias5 : n5=n1 := rfl
  have h_alias7 : n7=n1 := rfl
  simp only [h_alias2,h_alias4,h_alias5,h_alias7] at hcheck ⊢
  field_simp [hD]
  linear_combination hcheck

#print axioms values1

end Blueprint.Thomson.Finite.RFColumnProofs.Odd060
