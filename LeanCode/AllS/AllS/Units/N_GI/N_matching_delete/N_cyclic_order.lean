import AllS.Units.N_GI.N_cube_k6.N_shared_edge_geometry

set_option maxHeartbeats 300000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

/-- List the three positions after the removed position in a cyclic four-list. -/
def afterRemoved (k : Fin 4) (i : Fin 3) : Fin 4 := k+⟨i.val+1,by omega⟩

theorem afterRemoved_ne (k : Fin 4) (i : Fin 3) : afterRemoved k i≠k := by
  fin_cases k <;> fin_cases i <;> decide

theorem afterRemoved_injective (k : Fin 4) : Function.Injective (afterRemoved k) := by
  intro i j hij
  have hh := add_left_cancel hij
  exact Fin.ext (by have hn := congrArg Fin.val hh;dsimp at hn;omega)

def afterRemovedEquiv (k : Fin 4) : Fin 3 ≃ {j : Fin 4 // j≠k} :=
  Equiv.ofBijective (fun i => ⟨afterRemoved k i,afterRemoved_ne k i⟩) ⟨
    fun i j h => afterRemoved_injective k (congrArg Subtype.val h),by
      rintro ⟨j,hj⟩
      fin_cases k <;> fin_cases j
      all_goals try exact (hj rfl).elim
      all_goals first
        | exact ⟨0,Subtype.ext (by rfl)⟩
        | exact ⟨1,Subtype.ext (by rfl)⟩
        | exact ⟨2,Subtype.ext (by rfl)⟩⟩

theorem afterRemoved_next (k : Fin 4) (i : Fin 3) :
    afterRemoved k (i+1)=if afterRemoved k i+1=k then k+1 else afterRemoved k i+1 := by
  fin_cases k <;> fin_cases i <;> decide

theorem afterRemoved_previous (k : Fin 4) (i : Fin 3) :
    afterRemoved k (i+2)=if afterRemoved k i+3=k then k+3 else afterRemoved k i+3 := by
  fin_cases k <;> fin_cases i <;> decide

def eraseCyclicOrder {α : Type*} (e : Fin 4 ≃ α) (q : α) : Fin 3 ≃ {a : α // a≠q} :=
  (afterRemovedEquiv (e.symm q)).trans {
    toFun := fun a => ⟨e a.val,fun he => a.property (by simpa only [Equiv.symm_apply_apply] using congrArg e.symm he)⟩
    invFun := fun a => ⟨e.symm a.val,fun he => a.property (by simpa only [Equiv.apply_symm_apply] using congrArg e he)⟩
    left_inv := by intro a;apply Subtype.ext;exact e.symm_apply_apply a.val
    right_inv := by intro a;apply Subtype.ext;exact e.apply_symm_apply a.val }

@[simp] theorem eraseCyclicOrder_val {α : Type*} (e : Fin 4 ≃ α) (q : α) (i : Fin 3) :
    (eraseCyclicOrder e q i).val=e (afterRemoved (e.symm q) i) := rfl

theorem eraseCyclicOrder_previous {α : Type*} (e : Fin 4 ≃ α) (q : α) (i : Fin 3) :
    (eraseCyclicOrder e q (i+2)).val=
      if e (e.symm (eraseCyclicOrder e q i).val+3)=q then e (e.symm q+3)
      else e (e.symm (eraseCyclicOrder e q i).val+3) := by
  simp only [eraseCyclicOrder_val,Equiv.symm_apply_apply]
  rw [afterRemoved_previous]
  have hh (j : Fin 4) : e j=q ↔ j=e.symm q := by
    constructor
    · intro h;exact e.injective (h.trans (e.apply_symm_apply q).symm)
    · intro h;rw [h,e.apply_symm_apply]
  rw [hh]
  split_ifs <;> rfl

#print axioms eraseCyclicOrder_previous
end Blueprint.Thomson.Tail.Implementation
