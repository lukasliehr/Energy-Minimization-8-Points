import AllS.Units.N_FI.N_kernels.RFColumns.Standard004
import AllS.Units.N_FI.N_gram_map.N_family_and_map

noncomputable section
namespace Blueprint.Thomson.Finite.RFScalarFeatures.Standard004
open Blueprint.CAP RFCatalogue RFColumnProofs.Standard004
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem free_rows_5 : freeRows (standardTagList 5).length (standardPivots 5) = [2,4,5,7,8,9,10,13,15,16,17] := by
  simp only [standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Nat.reduceSub,Bool.false_eq_true,if_false,if_true,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  decide

theorem scalar_mdetStandard_7 (minus : Bool) (a : ℝ) (ha : physical a)
    (j : Fin (scalarBlockDimension .mdetStandard 7)) (hj : j.val=3) (h0 : rf0089.DefinedAt a) (h1 : rf0096.DefinedAt a) (h2 : rf0103.DefinedAt a) (h3 : rf0110.DefinedAt a) (h4 : rf0117.DefinedAt a) (h5 : rf0124.DefinedAt a) (h6 : rf0131.DefinedAt a) :
    rawColumn5 minus a=scalarFeature .mdetStandard a 7 (if minus then 1 else 0) j := by
  rw [raw_column_5 minus a ha h0 h1 h2 h3 h4 h5 h6]
  cases minus
  all_goals simp only [scalarFeature,scalarBlockFeatures,scalarS3PlusFeatures,scalarS3SignFeatures,scalarS3StandardFeatures,scalarS2Features,hj,Nat.reduceSub,Bool.false_eq_true,if_false,if_true]
  all_goals rw [free_rows_5]
  all_goals simp only [standardTagList,Nat.reduceSub,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  all_goals rfl
#print axioms scalar_mdetStandard_7

theorem free_rows_6 : freeRows (standardTagList 6).length (standardPivots 6) = [2,4,5,7,8,9,10,11,12,13,14,15,18,20,21,22,23,24,25,26] := by
  simp only [standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Nat.reduceSub,Bool.false_eq_true,if_false,if_true,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  decide

theorem scalar_m0Standard_6 (minus : Bool) (a : ℝ) (ha : physical a)
    (j : Fin (scalarBlockDimension .m0Standard 6)) (hj : j.val=3) (h0 : rf0089.DefinedAt a) (h1 : rf0096.DefinedAt a) (h2 : rf0103.DefinedAt a) (h3 : rf0110.DefinedAt a) (h4 : rf0117.DefinedAt a) (h5 : rf0124.DefinedAt a) (h6 : rf0131.DefinedAt a) :
    rawColumn6 minus a=scalarFeature .m0Standard a 6 (if minus then 1 else 0) j := by
  rw [raw_column_6 minus a ha h0 h1 h2 h3 h4 h5 h6]
  cases minus
  all_goals simp only [scalarFeature,scalarBlockFeatures,scalarS3PlusFeatures,scalarS3SignFeatures,scalarS3StandardFeatures,scalarS2Features,hj,Nat.reduceSub,Bool.false_eq_true,if_false,if_true]
  all_goals rw [free_rows_6]
  all_goals simp only [standardTagList,Nat.reduceSub,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  all_goals rfl
#print axioms scalar_m0Standard_6

theorem scalar_mdetStandard_8 (minus : Bool) (a : ℝ) (ha : physical a)
    (j : Fin (scalarBlockDimension .mdetStandard 8)) (hj : j.val=3) (h0 : rf0089.DefinedAt a) (h1 : rf0096.DefinedAt a) (h2 : rf0103.DefinedAt a) (h3 : rf0110.DefinedAt a) (h4 : rf0117.DefinedAt a) (h5 : rf0124.DefinedAt a) (h6 : rf0131.DefinedAt a) :
    rawColumn6 minus a=scalarFeature .mdetStandard a 8 (if minus then 1 else 0) j := by
  rw [raw_column_6 minus a ha h0 h1 h2 h3 h4 h5 h6]
  cases minus
  all_goals simp only [scalarFeature,scalarBlockFeatures,scalarS3PlusFeatures,scalarS3SignFeatures,scalarS3StandardFeatures,scalarS2Features,hj,Nat.reduceSub,Bool.false_eq_true,if_false,if_true]
  all_goals rw [free_rows_6]
  all_goals simp only [standardTagList,Nat.reduceSub,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  all_goals rfl
#print axioms scalar_mdetStandard_8

theorem free_rows_7 : freeRows (standardTagList 7).length (standardPivots 7) = [2,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,25,27,28,29,30,31,32,33,34,35,36,37,38] := by
  simp only [standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Nat.reduceSub,Bool.false_eq_true,if_false,if_true,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  decide

theorem scalar_m0Standard_7 (minus : Bool) (a : ℝ) (ha : physical a)
    (j : Fin (scalarBlockDimension .m0Standard 7)) (hj : j.val=3) (h0 : rf0089.DefinedAt a) (h1 : rf0096.DefinedAt a) (h2 : rf0103.DefinedAt a) (h3 : rf0110.DefinedAt a) (h4 : rf0117.DefinedAt a) (h5 : rf0124.DefinedAt a) (h6 : rf0131.DefinedAt a) :
    rawColumn7 minus a=scalarFeature .m0Standard a 7 (if minus then 1 else 0) j := by
  rw [raw_column_7 minus a ha h0 h1 h2 h3 h4 h5 h6]
  cases minus
  all_goals simp only [scalarFeature,scalarBlockFeatures,scalarS3PlusFeatures,scalarS3SignFeatures,scalarS3StandardFeatures,scalarS2Features,hj,Nat.reduceSub,Bool.false_eq_true,if_false,if_true]
  all_goals rw [free_rows_7]
  all_goals simp only [standardTagList,Nat.reduceSub,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  all_goals rfl
#print axioms scalar_m0Standard_7

theorem scalar_mdetStandard_9 (minus : Bool) (a : ℝ) (ha : physical a)
    (j : Fin (scalarBlockDimension .mdetStandard 9)) (hj : j.val=3) (h0 : rf0089.DefinedAt a) (h1 : rf0096.DefinedAt a) (h2 : rf0103.DefinedAt a) (h3 : rf0110.DefinedAt a) (h4 : rf0117.DefinedAt a) (h5 : rf0124.DefinedAt a) (h6 : rf0131.DefinedAt a) :
    rawColumn7 minus a=scalarFeature .mdetStandard a 9 (if minus then 1 else 0) j := by
  rw [raw_column_7 minus a ha h0 h1 h2 h3 h4 h5 h6]
  cases minus
  all_goals simp only [scalarFeature,scalarBlockFeatures,scalarS3PlusFeatures,scalarS3SignFeatures,scalarS3StandardFeatures,scalarS2Features,hj,Nat.reduceSub,Bool.false_eq_true,if_false,if_true]
  all_goals rw [free_rows_7]
  all_goals simp only [standardTagList,Nat.reduceSub,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  all_goals rfl
#print axioms scalar_mdetStandard_9

theorem free_rows_8 : freeRows (standardTagList 8).length (standardPivots 8) = [2,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,33,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53] := by
  simp only [standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Nat.reduceSub,Bool.false_eq_true,if_false,if_true,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  decide

theorem scalar_m0Standard_8 (minus : Bool) (a : ℝ) (ha : physical a)
    (j : Fin (scalarBlockDimension .m0Standard 8)) (hj : j.val=3) (h0 : rf0089.DefinedAt a) (h1 : rf0096.DefinedAt a) (h2 : rf0103.DefinedAt a) (h3 : rf0110.DefinedAt a) (h4 : rf0117.DefinedAt a) (h5 : rf0124.DefinedAt a) (h6 : rf0131.DefinedAt a) :
    rawColumn8 minus a=scalarFeature .m0Standard a 8 (if minus then 1 else 0) j := by
  rw [raw_column_8 minus a ha h0 h1 h2 h3 h4 h5 h6]
  cases minus
  all_goals simp only [scalarFeature,scalarBlockFeatures,scalarS3PlusFeatures,scalarS3SignFeatures,scalarS3StandardFeatures,scalarS2Features,hj,Nat.reduceSub,Bool.false_eq_true,if_false,if_true]
  all_goals rw [free_rows_8]
  all_goals simp only [standardTagList,Nat.reduceSub,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  all_goals rfl
#print axioms scalar_m0Standard_8

theorem free_rows_9 : freeRows (standardTagList 9).length (standardPivots 9) = [2,4,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,43,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71] := by
  simp only [standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Nat.reduceSub,Bool.false_eq_true,if_false,if_true,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  decide

theorem scalar_m0Standard_9 (minus : Bool) (a : ℝ) (ha : physical a)
    (j : Fin (scalarBlockDimension .m0Standard 9)) (hj : j.val=3) (h0 : rf0089.DefinedAt a) (h1 : rf0096.DefinedAt a) (h2 : rf0103.DefinedAt a) (h3 : rf0110.DefinedAt a) (h4 : rf0117.DefinedAt a) (h5 : rf0124.DefinedAt a) (h6 : rf0131.DefinedAt a) :
    rawColumn9 minus a=scalarFeature .m0Standard a 9 (if minus then 1 else 0) j := by
  rw [raw_column_9 minus a ha h0 h1 h2 h3 h4 h5 h6]
  cases minus
  all_goals simp only [scalarFeature,scalarBlockFeatures,scalarS3PlusFeatures,scalarS3SignFeatures,scalarS3StandardFeatures,scalarS2Features,hj,Nat.reduceSub,Bool.false_eq_true,if_false,if_true]
  all_goals rw [free_rows_9]
  all_goals simp only [standardTagList,Nat.reduceSub,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  all_goals rfl
#print axioms scalar_m0Standard_9

end Blueprint.Thomson.Finite.RFScalarFeatures.Standard004
