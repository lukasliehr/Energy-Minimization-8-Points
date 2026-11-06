import AllS.Units.N_FI.N_kernels.RFColumns.Even036_Fiber3PairGate
import AllS.Units.N_FI.N_kernels.RFColumns.Even036_Vector
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even036
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem values3 (a : ℝ) (ha : physical a) (h0 : rf0013.DefinedAt a) (h1 : rf0890.DefinedAt a) (h2 : rf0013.DefinedAt a) (h3 : rf0013.DefinedAt a) (h4 : rf0013.DefinedAt a) (h5 : rf0910.DefinedAt a) (h6 : rf0013.DefinedAt a) (h7 : rf0013.DefinedAt a) (h8 : rf0940.DefinedAt a) (h9 : rf0013.DefinedAt a) (h10 : rf0013.DefinedAt a) (h11 : rf0979.DefinedAt a) :
    ∀ j : Fin (parityFiberSize false 3),(∑ r,vector a r*(parityFiberU a false 3)^r.1.val*(parityFiberZ a false 3 j)^r.2.val)=paritySourceData a false (5,1,0) 3 j := by
  intro j
  have ha0 : a≠0 := by
    have hlo := lt_trans packing_endpoint_bounds.1 ha.1
    linarith
  have hD : evalQPoly den a≠0 := h0
  have hcheck:=RFParityList.checked_identity false 3 j Blueprint.Thomson.Finite.RFColumnProofs.Even036.PairData.terms Blueprint.Thomson.Finite.RFColumnProofs.Even036.PairData.denominator (5,1,0) (Blueprint.Thomson.Finite.RFColumnProofs.Even036.Fiber3PairGate.gate j) a
  simp only [Blueprint.Thomson.Finite.RFColumnProofs.Even036.PairData.terms,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hcheck
  simp only [Blueprint.Thomson.Finite.RFColumnProofs.Even036.PairData.num000_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even036.PairData.num001_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even036.PairData.num002_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even036.PairData.num003_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even036.PairData.num004_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even036.PairData.num005_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even036.PairData.num006_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even036.PairData.num007_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even036.PairData.num008_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even036.PairData.num009_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even036.PairData.num010_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even036.PairData.num011_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even036.PairData.denominator_eval] at hcheck
  rw [parity_sum_even]
  norm_num [vector,eval0 a h0 hD,eval1 a h1 hD,eval2 a h2 hD,eval3 a h3 hD,eval4 a h4 hD,eval5 a h5 hD,eval6 a h6 hD,eval7 a h7 hD,eval8 a h8 hD,eval9 a h9 hD,eval10 a h10 hD,eval11 a h11 hD]
  have h_alias2 : n2=n0 := rfl
  have h_alias3 : n3=n0 := rfl
  have h_alias4 : n4=n0 := rfl
  have h_alias6 : n6=n0 := rfl
  have h_alias7 : n7=n0 := rfl
  have h_alias9 : n9=n0 := rfl
  have h_alias10 : n10=n0 := rfl
  simp only [h_alias2,h_alias3,h_alias4,h_alias6,h_alias7,h_alias9,h_alias10] at hcheck ⊢
  field_simp [hD]
  linear_combination hcheck

#print axioms values3

end Blueprint.Thomson.Finite.RFColumnProofs.Even036
