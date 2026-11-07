import AllS.Units.N_GI.N_cube_k4_noE.N_pattern_counts

set_option maxHeartbeats 1800000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem cube_k4_noE_three_path_false (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=4)
    (v : Fin 4 → Fin 8) (hinj : Function.Injective v)
    (hfull : ∀z,Fintype.card (ContactNeighbor Y c z)=4 ↔ ∃i,v i=z)
    (hpat : ∀i j,(sharedTriangleGraph hY hc).Adj (v i) (v j) ↔ fourGraphAdj (fourPatternBits 0) i j) : False := by
  let S := sharedTriangleGraph hY hc
  let d := fun z => Fintype.card (ContactNeighbor Y c z)
  let t := faceCornerCount (boundaryArray Y c hY hc 3)
  let D := diagonalGraph hsupport
  have hs := auxiliary_graphs_shared_triangle_degrees Y c hY hc hcupper hirr hbound hne hsupport
  have ht := (rhombus_angles_assemble Y c hY hc hcupper hirr hbound hne hsupport).1
  have hd (z : Fin 8) : d z=3 ∨ d z=4 := by
    have hh := degree_degree_four Y c hY hc.1 hcupper hirr hbound z
      (covering_no_rattlers Y c hY hc hcupper hirr hbound hne hsupport z)
    rw [←contactNeighbor_card_eq] at hh
    change Fintype.card (ContactNeighbor Y c z)=3 ∨ Fintype.card (ContactNeighbor Y c z)=4
    omega
  have hth (z : Fin 8) (hz : d z=3) : t z≤1 := (ht z).1 hz
  have hv4 (i : Fin 4) : d (v i)=4 := (hfull _).mpr ⟨i,rfl⟩
  have hvne (i j : Fin 4) (h : i≠j) : v i≠v j := fun hh => h (hinj hh)
  have hn01 := hvne 0 1 (by decide)
  have hn02 := hvne 0 2 (by decide)
  have hn12 := hvne 1 2 (by decide)
  have hn30 := hvne 3 0 (by decide)
  have hn31 := hvne 3 1 (by decide)
  have hn32 := hvne 3 2 (by decide)
  have hs01 : S.Adj (v 0) (v 1) := (hpat 0 1).mpr (by decide +kernel)
  have hs12 : S.Adj (v 1) (v 2) := (hpat 1 2).mpr (by decide +kernel)
  have h01 := sharedTriangleGraph_subgraph hY hc hs01
  have h12 := sharedTriangleGraph_subgraph hY hc hs12
  have h02 : ContactAdj Y c (v 0) (v 2) := ⟨hn02,hs.2.2 (v 1) (v 0) (v 2) hn02 (S.adj_symm hs01) hs12⟩
  obtain ⟨f0,hf0⟩ := sharedTriangle_face_common hY hc hirr (v 0) (v 1) (v 2) hs01 h02 h12
  obtain ⟨a,fa,ha2,h0a,h1a,hfa⟩ := sharedTriangle_face_avoiding hY hc hirr (v 0) (v 1) (v 2) hs01
  obtain ⟨b,fb,hb0,h1b,h2b,hfb⟩ := sharedTriangle_face_avoiding hY hc hirr (v 1) (v 2) (v 0) hs12
  have ha0 := h0a.1.symm
  have ha1 := h1a.1.symm
  have hb1 := h1b.1.symm
  have hb2 := h2b.1.symm
  have hab : a≠b := by
    intro heq
    exact no_four_six_inner_products Y c hY.1 hc.1.le hcupper (v 0) (v 1) (v 2) a
      h01.2 h02.2 h0a.2 h12.2 h1a.2 (heq.symm ▸ h2b.2)
  have hSdeg (i : Fin 4) := (shared_pattern_degree S d 0 v hinj hfull hs.2.1 hpat i).trans (fourPattern_degrees 0 i)
  have ht1 : t (v 1)=3 := ((hs.1 (v 1)).2.1.mp (hSdeg 1)).2
  have ht3le : t (v 3)≤2 := by
    have hb : t (v 3)≤3 := (ht (v 3)).2 (hv4 3)
    have hS0 : S.degree (v 3)=0 := hSdeg 3
    have hn : t (v 3)≠3 := fun heq => by
      have hh := (hs.1 (v 3)).2.1.mpr ⟨hv4 3,heq⟩
      change S.degree (v 3)=2 at hh
      omega
    omega
  have hnotS1a : ¬S.Adj (v 1) a := by
    intro hsa
    obtain ⟨i,hi⟩ := (hfull a).mp (hs.2.1 _ _ hsa).2
    fin_cases i
    · exact ha0 hi.symm
    · exact ha1 hi.symm
    · exact ha2 hi.symm
    · have hh := (hpat 1 3).mp (hi.symm ▸ hsa)
      exact (by decide +kernel : ¬fourGraphAdj (fourPatternBits 0) 1 3) hh
  obtain ⟨z,hza,h1z,hnotS1z,hDaz⟩ := unshared_contact_opposite hY hc hcupper hirr hsupport (v 1) a h1a hnotS1a
  let f : Fin 4 → Fin 8 := ![v 0,v 2,a,b]
  have hf : Function.Injective f := by
    intro i j hh
    fin_cases i <;> fin_cases j
    all_goals try rfl
    all_goals dsimp [f] at hh
    all_goals first
      | exact (ha0 hh).elim | exact (ha0 hh.symm).elim
      | exact (ha2 hh).elim | exact (ha2 hh.symm).elim
      | exact (hb0 hh).elim | exact (hb0 hh.symm).elim
      | exact (hb2 hh).elim | exact (hb2 hh.symm).elim
      | exact (hab hh).elim | exact (hab hh.symm).elim
      | exact (hn02 hh).elim | exact (hn02 hh.symm).elim
  have hfc (i : Fin 4) : (actualContactGraph Y c).Adj (v 1) (f i) := by
    fin_cases i
    · exact (actualContactGraph Y c).adj_symm h01
    · exact h12
    · exact h1a
    · exact h1b
  obtain ⟨i,hi⟩ := graph_neighbors_exhaust (actualContactGraph Y c) (v 1) 4 f hf
    ((actualContactGraph_degree Y c (v 1)).trans (hv4 1)) hfc z h1z
  have hzb : z=b := by
    fin_cases i
    · exact (hnotS1z (hi ▸ S.adj_symm hs01)).elim
    · exact (hnotS1z (hi ▸ hs12)).elim
    · exact (hza hi.symm).elim
    · exact hi.symm
  have hDab : D.Adj a b := hzb ▸ hDaz
  have ha3 (hna : a≠v 3) : d a=3 := by
    rcases hd a with h3 | h4
    · exact h3
    · obtain ⟨i,hi⟩ := (hfull a).mp h4
      fin_cases i
      · exact (ha0 hi.symm).elim
      · exact (ha1 hi.symm).elim
      · exact (ha2 hi.symm).elim
      · exact (hna hi.symm).elim
  have hb3 (hnb : b≠v 3) : d b=3 := by
    rcases hd b with h3 | h4
    · exact h3
    · obtain ⟨i,hi⟩ := (hfull b).mp h4
      fin_cases i
      · exact (hb0 hi.symm).elim
      · exact (hb1 hi.symm).elim
      · exact (hb2 hi.symm).elim
      · exact (hnb hi.symm).elim
  have hta : 0<t a := triFace_mem_incidence_pos hsupport fa a (by simp [hfa])
  have htb : 0<t b := triFace_mem_incidence_pos hsupport fb b (by simp [hfb])
  have hnwa : v 3≠a := by
    intro heq
    have hdb : d b=3 := hb3 (by intro hh;exact hab (heq.symm.trans hh.symm))
    have htbone : t b=1 := by have hh:=hth b hdb;omega
    exact (diagonalGraph_no_mixed_types Y c hY hc hcupper hirr hbound hne hsupport (v 3) b (heq.symm ▸ hDab)).2.2
      ⟨hv4 3,ht3le,hdb,htbone⟩
  have hnwb : v 3≠b := by
    intro heq
    have hda : d a=3 := ha3 (by intro hh;exact hab (hh.trans heq))
    have htaone : t a=1 := by have hh:=hth a hda;omega
    exact (diagonalGraph_no_mixed_types Y c hY hc hcupper hirr hbound hne hsupport (v 3) a (heq.symm ▸ D.adj_symm hDab)).2.2
      ⟨hv4 3,ht3le,hda,htaone⟩
  have hf0a : f0≠fa := triFace_ne_of_member f0 fa (v 2)
    (by simp [hf0]) (by simp [hfa,hn02.symm,hn12.symm,ha2.symm])
  have hf0b : f0≠fb := triFace_ne_of_member f0 fb (v 0)
    (by simp [hf0]) (by simp [hfb,hn01,hn02,hb0.symm])
  have hfab : fa≠fb := triFace_ne_of_member fa fb (v 0)
    (by simp [hfa]) (by simp [hfb,hn01,hn02,hb0.symm])
  have hT : Fintype.card (TriFace Y c hY hc)=4 := by
    have hh := (sphere_euler_assemble Y c hY hc hcupper hirr hbound hne hsupport).2.2.1
    rw [hk] at hh
    exact hh
  have htw : t (v 3)≤1 := triangle_incidence_avoid_three hsupport hT f0 fa fb hf0a hf0b hfab (v 3)
    (by simp [hf0,hn30,hn31,hn32]) (by simp [hfa,hn30,hn31,hnwa]) (by simp [hfb,hn31,hn32,hnwb])
  have endpoint_type (j : Fin 4) (hSj : S.degree (v j)=1) : t (v j)=2 := by
    have hb : t (v j)≤3 := (ht (v j)).2 (hv4 j)
    have hh := sharedTriangleGraph_degree_four_cases hY hc (v j) (hv4 j) hb
    have hn3 : t (v j)≠3 := fun h => by have hs2:=hh.1.mpr h;change S.degree (v j)=2 at hs2;omega
    have hn1 : ¬t (v j)≤1 := fun h => by have hs0:=hh.2.2 h;change S.degree (v j)=0 at hs0;omega
    omega
  have ht0 : t (v 0)=2 := endpoint_type 0 (hSdeg 0)
  have ht2 : t (v 2)=2 := endpoint_type 2 (hSdeg 2)
  have hH : (Finset.univ.filter (fun z => d z=3 ∧ t z=1)).card=5-t (v 3) := by
    have hh := auxiliary_graphs_incidence_identity Y c hY hc hcupper hirr hbound hne hsupport
    change (∑z,if d z=4 then 3-t z else 0)=_ at hh
    rw [four_labels_deficiency d t v hinj hfull] at hh
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hh
    change (3-t (v 0))+((3-t (v 1))+((3-t (v 2))+(3-t (v 3))))=(Finset.univ.filter (fun z => d z=3 ∧ t z=1)).card at hh
    rw [ht0,ht1,ht2] at hh
    omega
  have hU : (Finset.univ.filter (fun z => d z=3 ∧ t z=0)).card=0 := by
    have hh := high_unused_count d t hth hk
    omega
  have hD1 : D.degree (v 1)=1 := (diagonalGraph_typed_degrees Y c hY hc hcupper hirr hsupport (v 1)).1 (hv4 1) ht1
  obtain ⟨w,hw⟩ := (D.degree_pos_iff_exists_adj (v 1)).mp (by omega)
  rcases hd w with h3 | h4
  · have hb := hth w h3
    have hn0 : t w≠0 := by
      intro hw0
      have hm : w∈Finset.univ.filter (fun z => d z=3 ∧ t z=0) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h3,hw0⟩
      have hh := Finset.card_pos.mpr ⟨w,hm⟩
      omega
    exact (diagonalGraph_no_mixed_types Y c hY hc hcupper hirr hbound hne hsupport (v 1) w hw).2.1
      ⟨hv4 1,ht1,h3,by change t w=1;omega⟩
  · obtain ⟨j,rfl⟩ := (hfull w).mp h4
    have hforbid (j : Fin 4) (hj : t (v j)≤2) : ¬D.Adj (v 1) (v j) := fun h =>
      (diagonalGraph_no_mixed_types Y c hY hc hcupper hirr hbound hne hsupport (v 1) (v j) h).1
        ⟨hv4 1,ht1,hv4 j,hj⟩
    fin_cases j
    · exact hforbid 0 (by omega) hw
    · exact D.irrefl hw
    · exact hforbid 2 (by omega) hw
    · exact hforbid 3 (by omega) hw

#print axioms cube_k4_noE_three_path_false
end Blueprint.Thomson.Tail.Implementation
