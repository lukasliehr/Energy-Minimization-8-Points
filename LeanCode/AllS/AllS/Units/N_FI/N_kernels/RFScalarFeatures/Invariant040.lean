import AllS.Units.N_FI.N_kernels.RFColumns.Invariant040
import AllS.Units.N_FI.N_gram_map.N_family_and_map

noncomputable section
namespace Blueprint.Thomson.Finite.RFScalarFeatures.Invariant040
open Blueprint.CAP RFCatalogue RFColumnProofs.Invariant040
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem free_rows_9 : freeRows (invariantTagList 9).length (invariantPivots 9) = [2,4,5,7,8,9,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52] := by
  simp only [standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Nat.reduceSub,Bool.false_eq_true,if_false,if_true,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  decide

theorem scalar_m0Plus_9 (a : ℝ) (ha : physical a)
    (j : Fin (scalarBlockDimension .m0Plus 9)) (hj : j.val=40) (h0 : rf0543.DefinedAt a) (h1 : rf0555.DefinedAt a) (h2 : rf0567.DefinedAt a) (h3 : rf0579.DefinedAt a) (h4 : rf0591.DefinedAt a) :
    rawColumn9 a=scalarFeature .m0Plus a 9 0 j := by
  rw [raw_column_9 a ha h0 h1 h2 h3 h4]
  all_goals simp only [scalarFeature,scalarBlockFeatures,scalarS3PlusFeatures,scalarS3SignFeatures,scalarS3StandardFeatures,scalarS2Features,hj,Nat.reduceSub,Bool.false_eq_true,if_false,if_true]
  all_goals rw [free_rows_9]
  all_goals simp only [standardTagList,Nat.reduceSub,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  all_goals rfl
#print axioms scalar_m0Plus_9

end Blueprint.Thomson.Finite.RFScalarFeatures.Invariant040
