import AllS.Units.N_FI.N_certificate.N_typed_contract
import AllS.Units.N_AI.N_data.Literals.extension_d18_c92_h2.Cell

set_option maxRecDepth 8192
noncomputable section
namespace Blueprint.CAP.Instances.extension_d18_c92_h2_GramLayout
open Blueprint.Thomson.Finite

def scalarOrder : ScalarBlockName → ℕ
  | .m0Plus => 48
  | .m0Sign => 21
  | .m0Standard => 65
  | .m1Even => 83
  | .m1Odd => 61
  | .mdetPlus => 26
  | .mdetSign => 9
  | .mdetStandard => 32

def pivots : MomentPivots 9 := fun k =>
  ⟨![0,1,0,1,0,0,0,0,0] k,by fin_cases k <;> decide⟩
def multiplicities : Fin 5 → ℕ := ![1,2,12,2,2]

def Statement : Prop :=
  (∀ b, scalarBlockDimension b 9=scalarOrder b) ∧ ValidMomentPivots pivots ∧
  Profile.Valid 18 multiplicities ∧
  List.ofFn (fun k => (pivots k).val)=Literals.extension_d18_c92_h2.value.momentPivots

theorem dimensions (b : ScalarBlockName) : scalarBlockDimension b 9=scalarOrder b := by
  cases b <;>
    simp only [scalarBlockDimension,scalarOrder,standardTagList,invariantPivots,
      signPivots,standardPivots,parityPivots,Nat.reduceSub,Bool.false_eq_true,
      if_false,if_true,RawCatalogue.invariantTagList_1,RawCatalogue.invariantTagList_2,RawCatalogue.invariantTagList_3,RawCatalogue.invariantTagList_4,RawCatalogue.invariantTagList_5,RawCatalogue.invariantTagList_6,RawCatalogue.invariantTagList_7,RawCatalogue.invariantTagList_8,RawCatalogue.invariantTagList_9,RawCatalogue.parityTagList_3,RawCatalogue.parityTagList_4,RawCatalogue.parityTagList_5,RawCatalogue.parityTagList_6,RawCatalogue.parityTagList_7,RawCatalogue.parityTagList_8,RawCatalogue.parityTagList_9] <;>
    decide +kernel

theorem pivots_valid : ValidMomentPivots pivots := by
  intro k
  fin_cases k
  · exact ⟨0,rfl⟩
  · exact ⟨6,rfl⟩
  · exact ⟨7,rfl⟩
  · exact ⟨3,rfl⟩
  · exact ⟨4,rfl⟩
  · exact ⟨5,rfl⟩
  · exact ⟨8,rfl⟩
  · exact ⟨9,rfl⟩
  · exact ⟨10,rfl⟩

theorem profile_valid : Profile.Valid 18 multiplicities := by
  unfold Profile.Valid
  constructor
  · norm_num [multiplicities,Fin.sum_univ_succ]
  · intro i hi
    fin_cases i <;> simp_all [multiplicities] <;> decide

theorem source_pivots :
    List.ofFn (fun k => (pivots k).val)=Literals.extension_d18_c92_h2.value.momentPivots := by
  decide +kernel

theorem sound : Statement := ⟨dimensions,pivots_valid,profile_valid,source_pivots⟩
#print Statement
#print axioms sound
end Blueprint.CAP.Instances.extension_d18_c92_h2_GramLayout
