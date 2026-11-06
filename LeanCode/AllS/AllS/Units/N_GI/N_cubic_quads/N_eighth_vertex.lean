import AllS.Units.N_GI.N_cubic_quads.N_seven_distinct

set_option maxHeartbeats 3000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem CubicQuadData.root_neighborFinset (Q : CubicQuadData) (o : Fin 8) :
    Q.graph.neighborFinset o=Finset.univ.image (Q.rootNeighbor o) := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
    exact (Q.graph.mem_neighborFinset o _).mpr (Q.order o i).property
  · rw [Q.graph.card_neighborFinset_eq_degree,Q.degree,
      Finset.card_image_of_injective _ (Q.rootNeighbor_injective o),Finset.card_univ,Fintype.card_fin]

theorem CubicQuadData.root_neighbor_neighborFinset (Q : CubicQuadData) (o : Fin 8) (i : Fin 3) :
    Q.graph.neighborFinset (Q.rootNeighbor o i) = {o,Q.rootOpposite o i,Q.rootOpposite o (i+2)} := by
  have hnext : i+2+1=i := by fin_cases i <;> decide
  have hprev : Q.graph.Adj (Q.rootNeighbor o i) (Q.rootOpposite o (i+2)) := by
    have h := (cubic_quads_root_faces Q o (i+2)).2.2.1.symm
    rwa [hnext] at h
  have hxi : Q.rootOpposite o i≠Q.rootOpposite o (i+2) :=
    (Q.rootOpposite_injective o).ne (by fin_cases i <;> decide)
  have hcard : ({o,Q.rootOpposite o i,Q.rootOpposite o (i+2)} : Finset (Fin 8)).card=3 := by
    have h1 : Q.rootOpposite o i∉({Q.rootOpposite o (i+2)} : Finset (Fin 8)) :=
      fun h => hxi (Finset.mem_singleton.mp h)
    have h2 : o∉({Q.rootOpposite o i,Q.rootOpposite o (i+2)} : Finset (Fin 8)) := by
      intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact Q.rootOpposite_ne_root o i h.symm
      · exact Q.rootOpposite_ne_root o (i+2) (Finset.mem_singleton.mp h).symm
    rw [Finset.card_insert_of_notMem h2,Finset.card_insert_of_notMem h1,Finset.card_singleton]
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro w hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with hw | hw | hw
    · subst w
      exact (Q.graph.mem_neighborFinset _ _).mpr (cubic_quads_root_faces Q o i).1.symm
    · subst w
      exact (Q.graph.mem_neighborFinset _ _).mpr (cubic_quads_root_faces Q o i).2.1
    · subst w
      exact (Q.graph.mem_neighborFinset _ _).mpr hprev
  · rw [Q.graph.card_neighborFinset_eq_degree,Q.degree,hcard]

theorem CubicQuadData.rootSeven_contains_neighbor (Q : CubicQuadData) (o : Fin 8) (i : Fin 3) :
    ∃ j, Q.rootSeven o j=Q.rootNeighbor o i := by
  fin_cases i
  · exact ⟨1,rfl⟩
  · exact ⟨2,rfl⟩
  · exact ⟨3,rfl⟩

theorem CubicQuadData.rootSeven_contains_opposite (Q : CubicQuadData) (o : Fin 8) (i : Fin 3) :
    ∃ j, Q.rootSeven o j=Q.rootOpposite o i := by
  fin_cases i
  · exact ⟨4,rfl⟩
  · exact ⟨5,rfl⟩
  · exact ⟨6,rfl⟩

theorem cubic_quads_eighth_vertex (Q : CubicQuadData) (o : Fin 8) :
    ∃ z : Fin 8, (∀ j, Q.rootSeven o j≠z) ∧
      Q.graph.neighborFinset z=Finset.univ.image (Q.rootOpposite o) := by
  have hns : ¬ Function.Surjective (Q.rootSeven o) := by
    intro hsurj
    have hh := Fintype.card_le_of_surjective _ hsurj
    norm_num at hh
  simp only [Function.Surjective,not_forall,not_exists] at hns
  obtain ⟨z,hz⟩ := hns
  have hz0 : z≠o := fun h => hz 0 h.symm
  have hza (i : Fin 3) : z≠Q.rootNeighbor o i := by
    obtain ⟨j,hj⟩ := Q.rootSeven_contains_neighbor o i
    exact fun h => hz j (hj.trans h.symm)
  have hzx (i : Fin 3) : z≠Q.rootOpposite o i := by
    obtain ⟨j,hj⟩ := Q.rootSeven_contains_opposite o i
    exact fun h => hz j (hj.trans h.symm)
  have hno0 : ¬Q.graph.Adj z o := by
    intro hadj
    have hm := (Q.graph.mem_neighborFinset o z).mpr hadj.symm
    rw [Q.root_neighborFinset o] at hm
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hm
    exact hza i hi.symm
  have hnoa (i : Fin 3) : ¬Q.graph.Adj z (Q.rootNeighbor o i) := by
    intro hadj
    have hm := (Q.graph.mem_neighborFinset _ z).mpr hadj.symm
    rw [Q.root_neighbor_neighborFinset o i] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    exact hm.elim hz0 (fun h => h.elim (hzx i) (hzx (i+2)))
  let S := Finset.univ.image (Q.rootSeven o)
  have hScard : S.card=7 := by
    rw [Finset.card_image_of_injective _ (cubic_quads_seven_distinct Q o),Finset.card_univ,Fintype.card_fin]
  have hzS : z∉S := by
    rintro hm
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hm
    exact hz j hj
  have hcover : insert z S=Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_insert_of_notMem hzS,hScard,Finset.card_univ,Fintype.card_fin]
  have hsub : Q.graph.neighborFinset z ⊆ Finset.univ.image (Q.rootOpposite o) := by
    intro w hw
    have hadj := (Q.graph.mem_neighborFinset z w).mp hw
    have hm : w∈insert z S := by rw [hcover]; exact Finset.mem_univ _
    rcases Finset.mem_insert.mp hm with rfl | hm
    · exact (Q.graph.irrefl hadj).elim
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hm
      fin_cases j
      · exact (hno0 hadj).elim
      · exact (hnoa 0 hadj).elim
      · exact (hnoa 1 hadj).elim
      · exact (hnoa 2 hadj).elim
      · exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩
      · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩
      · exact Finset.mem_image.mpr ⟨2,Finset.mem_univ _,rfl⟩
  refine ⟨z,hz,Finset.eq_of_subset_of_card_le hsub ?_⟩
  rw [Finset.card_image_of_injective _ (Q.rootOpposite_injective o),Finset.card_univ,Fintype.card_fin,
    Q.graph.card_neighborFinset_eq_degree,Q.degree]

#print axioms CubicQuadData.root_neighbor_neighborFinset
#print axioms cubic_quads_eighth_vertex
end Blueprint.Thomson.Tail.Implementation
