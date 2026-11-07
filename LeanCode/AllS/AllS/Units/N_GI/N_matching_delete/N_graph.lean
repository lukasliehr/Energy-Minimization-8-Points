import AllS.Units.N_GI.N_matching_delete.N_cyclic_order

set_option maxHeartbeats 300000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

def graphWithout (G M : SimpleGraph (Fin 8)) : SimpleGraph (Fin 8) where
  Adj v w := G.Adj v w ∧ ¬M.Adj v w
  symm := ⟨fun v w h => ⟨G.adj_symm h.1,fun hm => h.2 (M.adj_symm hm)⟩⟩
  loopless := ⟨fun v h => G.irrefl h.1⟩

theorem graphWithout_neighborFinset (G M : SimpleGraph (Fin 8)) (v : Fin 8) :
    (graphWithout G M).neighborFinset v=G.neighborFinset v\M.neighborFinset v := by
  apply Finset.ext
  intro w
  simp only [SimpleGraph.mem_neighborFinset,Finset.mem_sdiff]
  rfl

theorem graphWithout_degree (G M : SimpleGraph (Fin 8)) (hM : M≤G) (v : Fin 8) :
    (graphWithout G M).degree v=G.degree v-M.degree v := by
  change ((graphWithout G M).neighborFinset v).card= (G.neighborFinset v).card-(M.neighborFinset v).card
  rw [graphWithout_neighborFinset]
  apply Finset.card_sdiff_of_subset
  intro w hw
  exact (G.mem_neighborFinset _ _).mpr (hM ((M.mem_neighborFinset _ _).mp hw))

def deletedNeighborEquiv (G M : SimpleGraph (Fin 8)) (v : Fin 8) :
    (graphWithout G M).neighborSet v ≃ {q : G.neighborSet v // ¬M.Adj v q.val} where
  toFun q := ⟨⟨q.val,q.property.1⟩,q.property.2⟩
  invFun q := ⟨q.val.val,q.val.property,q.property⟩
  left_inv q := rfl
  right_inv q := rfl

def retainedNeighborEquivOfZero (G M : SimpleGraph (Fin 8)) (v : Fin 8)
    (hzero : M.degree v=0) : G.neighborSet v ≃ (graphWithout G M).neighborSet v where
  toFun q := ⟨q.val,q.property,fun hm => by
    have hh := (M.degree_pos_iff_exists_adj v).mpr ⟨q.val,hm⟩
    omega⟩
  invFun q := ⟨q.val,q.property.1⟩
  left_inv q := rfl
  right_inv q := rfl

def retainedNeighborEquivOfOne (G M : SimpleGraph (Fin 8)) (v : Fin 8)
    (q : G.neighborSet v) (honly : ∀ w,M.Adj v w ↔ w=q.val) :
    {r : G.neighborSet v // r≠q} ≃ (graphWithout G M).neighborSet v where
  toFun r := ⟨r.val.val,r.val.property,fun hm => r.property (Subtype.ext ((honly _).mp hm))⟩
  invFun r := ⟨⟨r.val,r.property.1⟩,fun he => r.property.2 ((honly _).mpr (congrArg Subtype.val he))⟩
  left_inv r := rfl
  right_inv r := rfl

theorem degree_one_unique_neighbor (G M : SimpleGraph (Fin 8)) (hM : M≤G)
    (v : Fin 8) (hone : M.degree v=1) :
    ∃ q : G.neighborSet v,∀w,M.Adj v w ↔ w=q.val := by
  have hc : (M.neighborFinset v).card=1 := hone
  obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hc
  have hadj : M.Adj v w := (M.mem_neighborFinset _ _).mp (hw ▸ Finset.mem_singleton_self w)
  refine ⟨⟨w,hM hadj⟩,fun x => ?_⟩
  rw [←M.mem_neighborFinset,hw,Finset.mem_singleton]

#print axioms graphWithout_degree
#print axioms degree_one_unique_neighbor
end Blueprint.Thomson.Tail.Implementation
