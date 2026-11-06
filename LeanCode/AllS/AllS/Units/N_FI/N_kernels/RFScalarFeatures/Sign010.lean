import AllS.Units.N_FI.N_kernels.RFColumns.Sign010
import AllS.Units.N_FI.N_gram_map.N_family_and_map

noncomputable section
namespace Blueprint.Thomson.Finite.RFScalarFeatures.Sign010
open Blueprint.CAP RFCatalogue RFColumnProofs.Sign010
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem free_rows_8 : freeRows (invariantTagList (8-3)).length (signPivots 8) = [2,3,4,5,6,7,8,9,10,11,12,13,14,15] := by
  simp only [standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Nat.reduceSub,Bool.false_eq_true,if_false,if_true,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  decide

theorem scalar_m0Sign_8 (a : ℝ) (ha : physical a)
    (j : Fin (scalarBlockDimension .m0Sign 8)) (hj : j.val=10) (h0 : rf0425.DefinedAt a) (h1 : rf0430.DefinedAt a) :
    rawColumn8 a=scalarFeature .m0Sign a 8 0 j := by
  rw [raw_column_8 a ha h0 h1]
  all_goals simp only [scalarFeature,scalarBlockFeatures,scalarS3PlusFeatures,scalarS3SignFeatures,scalarS3StandardFeatures,scalarS2Features,hj,Nat.reduceSub,Bool.false_eq_true,if_false,if_true]
  all_goals rw [free_rows_8]
  all_goals simp only [standardTagList,Nat.reduceSub,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  all_goals rfl
#print axioms scalar_m0Sign_8

theorem free_rows_9 : freeRows (invariantTagList (9-3)).length (signPivots 9) = [2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22] := by
  simp only [standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Nat.reduceSub,Bool.false_eq_true,if_false,if_true,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  decide

theorem scalar_m0Sign_9 (a : ℝ) (ha : physical a)
    (j : Fin (scalarBlockDimension .m0Sign 9)) (hj : j.val=10) (h0 : rf0425.DefinedAt a) (h1 : rf0430.DefinedAt a) :
    rawColumn9 a=scalarFeature .m0Sign a 9 0 j := by
  rw [raw_column_9 a ha h0 h1]
  all_goals simp only [scalarFeature,scalarBlockFeatures,scalarS3PlusFeatures,scalarS3SignFeatures,scalarS3StandardFeatures,scalarS2Features,hj,Nat.reduceSub,Bool.false_eq_true,if_false,if_true]
  all_goals rw [free_rows_9]
  all_goals simp only [standardTagList,Nat.reduceSub,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  all_goals rfl
#print axioms scalar_m0Sign_9

end Blueprint.Thomson.Finite.RFScalarFeatures.Sign010
