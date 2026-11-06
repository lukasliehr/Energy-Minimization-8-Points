import AllS.Units.N_AI.N_fixed_tables.D18.Data
import AllS.Units.N_AI.N_fixed_tables.LayoutSupport

noncomputable section
namespace Blueprint.CAP.FixedTables.D18
open Blueprint.Thomson.Finite
set_option maxHeartbeats 0
set_option maxRecDepth 272000

theorem coordinateTags_source : List.ofFn coordinateTags=retainedTagList 18 := by
  exact (fixedRetainedList_literal 18 _ (by decide +kernel) (by decide +kernel) (by decide +kernel)).symm

theorem retainedTagList_length : (retainedTagList 18).length=272 := by
  rw [← coordinateTags_source,List.length_ofFn]

def retainedIndex (i : Fin 272) : RetainedIndex 18 :=
  retainedTagEnum 18 ⟨i.val,by rw [retainedTagList_length];exact i.isLt⟩

theorem retainedIndex_tag (i : Fin 272) : (retainedIndex i).val=coordinateTags i := by
  simp only [retainedIndex,retainedTagEnum_apply]
  simp only [← coordinateTags_source,List.get_eq_getElem,List.getElem_ofFn]

theorem retainedIndex_bijective : Function.Bijective retainedIndex := by
  constructor
  · intro i j hij
    have h := (retainedTagEnum 18).injective hij
    exact Fin.ext (congrArg (fun x : Fin (retainedTagList 18).length => x.val) h)
  · intro t
    obtain ⟨i,hi⟩ := (retainedTagEnum 18).surjective t
    refine ⟨⟨i.val,by rw [← retainedTagList_length];exact i.isLt⟩,?_⟩
    exact hi

#print axioms coordinateTags_source
#print axioms retainedIndex_bijective
end Blueprint.CAP.FixedTables.D18
