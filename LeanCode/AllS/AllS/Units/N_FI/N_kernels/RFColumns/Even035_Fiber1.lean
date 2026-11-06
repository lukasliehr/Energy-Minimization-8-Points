import AllS.Units.N_FI.N_kernels.RFColumns.Even035_Fiber1PairGate
import AllS.Units.N_FI.N_kernels.RFColumns.Even035_Vector
import AllS.Units.N_FI.N_kernels.RFColumnBridge
import AllS.Units.N_FI.N_moment_kernels.N_candidate_factor
import AllS.Generated.FiniteKernelRFCatalogue.Chunk0
import AllS.Generated.FiniteKernelRFCatalogue.Chunk1

noncomputable section
open scoped BigOperators
namespace Blueprint.Thomson.Finite.RFColumnProofs.Even035
open Blueprint.CAP RFCatalogue RFBridge
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem values1 (a : ℝ) (ha : physical a) (h0 : rf1066.DefinedAt a) (h1 : rf0013.DefinedAt a) (h2 : rf1109.DefinedAt a) (h3 : rf0013.DefinedAt a) (h4 : rf1094.DefinedAt a) (h5 : rf0013.DefinedAt a) (h6 : rf1164.DefinedAt a) (h7 : rf1136.DefinedAt a) (h8 : rf0013.DefinedAt a) (h9 : rf1206.DefinedAt a) (h10 : rf1191.DefinedAt a) (h11 : rf0013.DefinedAt a) :
    ∀ j : Fin (parityFiberSize false 1),(∑ r,vector a r*(parityFiberU a false 1)^r.1.val*(parityFiberZ a false 1 j)^r.2.val)=paritySourceData a false (4,2,0) 1 j := by
  intro j
  have ha0 : a≠0 := by
    have hlo := lt_trans packing_endpoint_bounds.1 ha.1
    linarith
  have hD : evalQPoly den a≠0 := h0
  have hcheck:=RFParityList.checked_identity false 1 j Blueprint.Thomson.Finite.RFColumnProofs.Even035.PairData.terms Blueprint.Thomson.Finite.RFColumnProofs.Even035.PairData.denominator (4,2,0) (Blueprint.Thomson.Finite.RFColumnProofs.Even035.Fiber1PairGate.gate j) a
  simp only [Blueprint.Thomson.Finite.RFColumnProofs.Even035.PairData.terms,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hcheck
  simp only [Blueprint.Thomson.Finite.RFColumnProofs.Even035.PairData.num000_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even035.PairData.num001_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even035.PairData.num002_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even035.PairData.num003_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even035.PairData.num004_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even035.PairData.num005_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even035.PairData.num006_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even035.PairData.num007_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even035.PairData.num008_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even035.PairData.num009_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even035.PairData.num010_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even035.PairData.num011_eval,Blueprint.Thomson.Finite.RFColumnProofs.Even035.PairData.denominator_eval] at hcheck
  rw [parity_sum_even]
  norm_num [vector,eval0 a h0 hD,eval1 a h1 hD,eval2 a h2 hD,eval3 a h3 hD,eval4 a h4 hD,eval5 a h5 hD,eval6 a h6 hD,eval7 a h7 hD,eval8 a h8 hD,eval9 a h9 hD,eval10 a h10 hD,eval11 a h11 hD]
  have h_alias3 : n3=n1 := rfl
  have h_alias5 : n5=n1 := rfl
  have h_alias8 : n8=n1 := rfl
  have h_alias11 : n11=n1 := rfl
  simp only [h_alias3,h_alias5,h_alias8,h_alias11] at hcheck ⊢
  field_simp [hD]
  linear_combination hcheck

#print axioms values1

end Blueprint.Thomson.Finite.RFColumnProofs.Even035
