import AllS.Units.N_GI.N_matching_delete.N_graph

set_option maxHeartbeats 500000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem cyclicOrder_previous_three {α : Type*} (p : Equiv.Perm α) (e : Fin 3 ≃ α)
    (he : ∀i,p (e i)=e (i+1)) (i : Fin 3) : p.symm (e i)=e (i+2) := by
  apply p.injective
  rw [Equiv.apply_symm_apply,he]
  congr 1
  fin_cases i <;> decide

theorem cyclicOrder_previous_four {α : Type*} (p : Equiv.Perm α) (e : Fin 4 ≃ α)
    (he : ∀i,p (e i)=e (i+1)) (i : Fin 4) : p.symm (e i)=e (i+3) := by
  apply p.injective
  rw [Equiv.apply_symm_apply,he]
  congr 1
  fin_cases i <;> decide

def retainedToOriginal (G M : SimpleGraph (Fin 8)) (v : Fin 8)
    (q : (graphWithout G M).neighborSet v) : G.neighborSet v := ⟨q.val,q.property.1⟩

theorem eraseCyclicOrder_previous_perm {α : Type*} (p : Equiv.Perm α) (e : Fin 4 ≃ α)
    (he : ∀i,p (e i)=e (i+1)) (q : α) (i : Fin 3) :
    (eraseCyclicOrder e q (i+2)).val=
      if p.symm (eraseCyclicOrder e q i).val=q then p.symm q
      else p.symm (eraseCyclicOrder e q i).val := by
  have hp (a : α) : p.symm a=e (e.symm a+3) := by
    simpa only [Equiv.apply_symm_apply] using cyclicOrder_previous_four p e he (e.symm a)
  simpa only [hp] using eraseCyclicOrder_previous e q i

theorem deleted_order_three (G M : SimpleGraph (Fin 8)) (v : Fin 8)
    (hMzero : M.degree v=0) (p : Equiv.Perm (G.neighborSet v)) (e : Fin 3 ≃ G.neighborSet v)
    (he : ∀i,p (e i)=e (i+1)) :
    ∃ e' : Fin 3 ≃ (graphWithout G M).neighborSet v,∀i,
      (e' (i+2)).val=
        if M.Adj v (p.symm (retainedToOriginal G M v (e' i))).val then
          (p.symm (p.symm (retainedToOriginal G M v (e' i)))).val
        else (p.symm (retainedToOriginal G M v (e' i))).val := by
  let e' := e.trans (retainedNeighborEquivOfZero G M v hMzero)
  refine ⟨e',fun i => ?_⟩
  have hn (r : G.neighborSet v) : ¬M.Adj v r.val := by
    intro hm
    have hh := (M.degree_pos_iff_exists_adj v).mpr ⟨r.val,hm⟩
    omega
  rw [if_neg (hn _)]
  change (e (i+2)).val=(p.symm (e i)).val
  rw [cyclicOrder_previous_three p e he]

theorem deleted_order_four (G M : SimpleGraph (Fin 8)) (hM : M≤G) (v : Fin 8)
    (hMone : M.degree v=1) (p : Equiv.Perm (G.neighborSet v)) (e : Fin 4 ≃ G.neighborSet v)
    (he : ∀i,p (e i)=e (i+1)) :
    ∃ e' : Fin 3 ≃ (graphWithout G M).neighborSet v,∀i,
      (e' (i+2)).val=
        if M.Adj v (p.symm (retainedToOriginal G M v (e' i))).val then
          (p.symm (p.symm (retainedToOriginal G M v (e' i)))).val
        else (p.symm (retainedToOriginal G M v (e' i))).val := by
  obtain ⟨q,hq⟩ := degree_one_unique_neighbor G M hM v hMone
  let e' := (eraseCyclicOrder e q).trans (retainedNeighborEquivOfOne G M v q hq)
  refine ⟨e',fun i => ?_⟩
  change (eraseCyclicOrder e q (i+2)).val.val=
    if M.Adj v (p.symm (eraseCyclicOrder e q i).val).val then
      (p.symm (p.symm (eraseCyclicOrder e q i).val)).val
    else (p.symm (eraseCyclicOrder e q i).val).val
  rw [eraseCyclicOrder_previous_perm p e he]
  have hh (r : G.neighborSet v) : M.Adj v r.val ↔ r=q := by
    exact (hq r.val).trans ⟨Subtype.ext,congrArg Subtype.val⟩
  rw [hh]
  split_ifs with h
  · rw [h]
  · rfl

#print axioms deleted_order_three
#print axioms deleted_order_four
end Blueprint.Thomson.Tail.Implementation
