import AllS.Units.N_FI.N_kernels.RFColumns.Odd048
import AllS.Units.N_FI.N_gram_map.N_family_and_map

noncomputable section
namespace Blueprint.Thomson.Finite.RFScalarFeatures.Odd048
open Blueprint.CAP RFCatalogue RFColumnProofs.Odd048
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

theorem free_rows_8 : freeRows (parityTagList (8-1)).length (parityPivots true 8) = [3,7,8,9,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69] := by
  simp only [standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Nat.reduceSub,Bool.false_eq_true,if_false,if_true,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  decide

theorem scalar_m1Odd_9 (a : ℝ) (ha : physical a)
    (j : Fin (scalarBlockDimension .m1Odd 9)) (hj : j.val=48) (h0 : rf1932.DefinedAt a) (h1 : rf1951.DefinedAt a) (h2 : rf1988.DefinedAt a) (h3 : rf1969.DefinedAt a) (h4 : rf2006.DefinedAt a) (h5 : rf2043.DefinedAt a) (h6 : rf2024.DefinedAt a) (h7 : rf2061.DefinedAt a) (h8 : rf2079.DefinedAt a) :
    rawColumn8 a=scalarFeature .m1Odd a 9 0 j := by
  rw [raw_column_8 a ha h0 h1 h2 h3 h4 h5 h6 h7 h8]
  all_goals simp only [scalarFeature,scalarBlockFeatures,scalarS3PlusFeatures,scalarS3SignFeatures,scalarS3StandardFeatures,scalarS2Features,hj,Nat.reduceSub,Bool.false_eq_true,if_false,if_true]
  all_goals rw [free_rows_8]
  all_goals simp only [standardTagList,Nat.reduceSub,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  all_goals rfl
#print axioms scalar_m1Odd_9

theorem free_rows_9 : freeRows (parityTagList (9-1)).length (parityPivots true 9) = [3,7,8,9,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94] := by
  simp only [standardTagList,invariantPivots,signPivots,standardPivots,parityPivots,Nat.reduceSub,Bool.false_eq_true,if_false,if_true,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9]
  decide

end Blueprint.Thomson.Finite.RFScalarFeatures.Odd048
