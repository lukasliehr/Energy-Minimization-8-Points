import AllS.Units.N_GI.N_matching_delete.N_shared_edges

set_option maxHeartbeats 700000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem cube_k6_shared_edge_delete (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=6) :
    ∃ f g : TriFace Y c hY hc,∃u v : Fin 8,f≠g ∧ u≠v ∧
      triFaceVertices f∩triFaceVertices g={u,v} ∧
      (∀a b,(sharedTriangleGraph hY hc).Adj a b ↔ (a=u ∧ b=v) ∨ (a=v ∧ b=u)) ∧
      ∃ e : CubeVertex ≃ Fin 8,∀a b : CubeVertex,
        (graphWithout (actualContactGraph Y c) (sharedTriangleGraph hY hc)).Adj (e a) (e b) ↔
          a.1≠b.1 ∧ a.2≠b.2 := by
  let S := sharedTriangleGraph hY hc
  let d := fun v => Fintype.card (ContactNeighbor Y c v)
  obtain ⟨f,g,hfg,hfaces⟩ := two_triangles_exhaust Y c hY hc hcupper hirr hbound hne hsupport hk
  obtain ⟨u,v,huv,hinter,hcontact⟩ := cube_k6_shared_edge Y c hY hc hcupper hirr hbound hne hsupport hk f g hfg
  have hu : u∈triFaceVertices f∩triFaceVertices g := by rw [hinter];exact Finset.mem_insert_self _ _
  have hv : v∈triFaceVertices f∩triFaceVertices g := by rw [hinter];exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hSuv : S.Adj u v := triFaces_common_edge_shared f g hfg u v hcontact
    (Finset.mem_inter.mp hu).1 (Finset.mem_inter.mp hv).1 (Finset.mem_inter.mp hu).2 (Finset.mem_inter.mp hv).2
  have ha := covering_no_rattlers Y c hY hc hcupper hirr hbound hne hsupport
  have hd (z : Fin 8) : d z=3 ∨ d z=4 := by
    have hh := degree_degree_four Y c hY hc.1 hcupper hirr hbound z (ha z)
    rw [←contactNeighbor_card_eq] at hh
    change Fintype.card (ContactNeighbor Y c z)=3 ∨ Fintype.card (ContactNeighbor Y c z)=4
    omega
  have hs := auxiliary_graphs_shared_triangle_degrees Y c hY hc hcupper hirr hbound hne hsupport
  have hu4 : d u=4 := (hs.2.1 u v hSuv).1
  have hv4 : d v=4 := (hs.2.1 u v hSuv).2
  have hcard4 : (Finset.univ.filter (fun z => d z=4)).card=2 := by
    have hh := degree_three_four_count d hd
    have h3 : (Finset.univ.filter (fun z => d z=3)).card=6 := hk
    omega
  have hfourset : (Finset.univ.filter (fun z => d z=4))={u,v} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      have hh : z=u ∨ z=v := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hz
      rcases hh with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hu4⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv4⟩
    · rw [hcard4,Finset.card_pair huv]
  have hfour (z : Fin 8) (hz : d z=4) : z=u ∨ z=v := by
    have hm : z∈Finset.univ.filter (fun z => d z=4) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz⟩
    rw [hfourset] at hm
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
  have hSgraph (a b : Fin 8) : S.Adj a b ↔ (a=u ∧ b=v) ∨ (a=v ∧ b=u) := by
    constructor
    · intro hab
      have hh := hs.2.1 a b hab
      rcases hfour a hh.1 with rfl | rfl <;> rcases hfour b hh.2 with rfl | rfl
      · exact (S.irrefl hab).elim
      · exact Or.inl ⟨rfl,rfl⟩
      · exact Or.inr ⟨rfl,rfl⟩
      · exact (S.irrefl hab).elim
    · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩)
      · exact hSuv
      · exact S.adj_symm hSuv
  have htbound (z : Fin 8) : faceCornerCount (boundaryArray Y c hY hc 3) z≤2 := by
    rw [triFace_pair_indicator f g hfg hfaces hsupport z]
    split_ifs <;> omega
  have hSle (z : Fin 8) : S.degree z≤1 := by
    rcases hd z with h3 | h4
    · have hh := (hs.1 z).2.2 h3
      change S.degree z=0 at hh
      omega
    · exact (sharedTriangleGraph_degree_four_cases hY hc z h4 (by have hh:=htbound z;omega)).2.1 (htbound z)
  have hSdegree (z : Fin 8) : S.degree z+3=d z := by
    rcases hd z with h3 | h4
    · have hh := (hs.1 z).2.2 h3
      change S.degree z=0 at hh
      omega
    · have hpos : 0<S.degree z := by
        rcases hfour z h4 with rfl | rfl
        · exact (S.degree_pos_iff_exists_adj _).mpr ⟨v,hSuv⟩
        · exact (S.degree_pos_iff_exists_adj _).mpr ⟨u,S.adj_symm hSuv⟩
      have hle := hSle z
      omega
  have hside (h : TriFace Y c hY hc) : ∃i : Fin 3,S.Adj (triFaceVertex h i) (triFaceVertex h (i+1)) := by
    have hhu : u∈triFaceVertices h := by
      rcases hfaces h with rfl | rfl
      · exact (Finset.mem_inter.mp hu).1
      · exact (Finset.mem_inter.mp hu).2
    have hhv : v∈triFaceVertices h := by
      rcases hfaces h with rfl | rfl
      · exact (Finset.mem_inter.mp hv).1
      · exact (Finset.mem_inter.mp hv).2
    rcases triFace_oriented_index h u v huv hhu hhv with ⟨i,hi,hi'⟩ | ⟨i,hi,hi'⟩
    · exact ⟨i,(congrArg₂ S.Adj hi hi').mpr hSuv⟩
    · exact ⟨i,(congrArg₂ S.Adj hi hi').mpr (S.adj_symm hSuv)⟩
  let Q := matchingDeletedQuad hY hc hcupper hirr hbound hsupport S (sharedTriangleGraph_subgraph hY hc)
    hd hSdegree (sharedTriangleGraph_flag hY hc) (triangle_deletion_from_face_sides hY hc S hside)
  exact ⟨f,g,u,v,hfg,huv,hinter,hSgraph,cubic_quads_assemble Q⟩

theorem cube_k6_has_spanning_cube (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=6) : HasSpanningCube (actualContactGraph Y c) := by
  obtain ⟨f,g,u,v,hfg,huv,hinter,hS,e,he⟩ := cube_k6_shared_edge_delete Y c hY hc hcupper hirr hbound hne hsupport hk
  refine ⟨e,fun i j hij => ?_⟩
  exact ((he (0,i) (1,j)).mpr ⟨by change (0:Fin 2)≠1;decide,hij⟩).1

#print axioms cube_k6_shared_edge_delete
#print axioms cube_k6_has_spanning_cube
end Blueprint.Thomson.Tail.Implementation
