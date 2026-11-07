import AllS.Units.N_GI.N_cube_k6.N_disjoint_geometry
import AllS.Units.N_GI.N_cube_k6.N_single_vertex_labeling

set_option maxHeartbeats 300000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem two_degree_four_labels (d : Fin 8 → ℕ)
    (hc : (Finset.univ.filter (fun i => d i=4)).card=2) (hzero : d 0=4) :
    ∃ y : Fin 8,y≠0 ∧ ∀i,d i=4 ↔ i=0 ∨ i=y := by
  obtain ⟨x,y,hxy,hpair⟩ := Finset.card_eq_two.mp hc
  have hm (i : Fin 8) : d i=4 ↔ i=x ∨ i=y := by
    have hh : i∈Finset.univ.filter (fun i => d i=4) ↔ i∈({x,y} : Finset (Fin 8)) := by rw [hpair]
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton] using hh
  rcases (hm 0).mp hzero with h | h
  · subst x
    exact ⟨y,hxy.symm,hm⟩
  · subst y
    refine ⟨x,hxy,fun i => ?_⟩
    exact (hm i).trans or_comm

theorem contact_with_no_shared_edge_has_quad {Y : Fin 8 → Point} {c : ℝ}
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (v w : Fin 8) (hadj : ContactAdj Y c v w)
    (hszero : (sharedTriangleGraph hY hc).degree w=0) :
    ∃ f : QuadFace Y c hY hc, ∃ i : Fin 4,
      quadFaceVertex f i=v ∧ (quadFaceVertex f (i+1)=w ∨ quadFaceVertex f (i+3)=w) := by
  let q : ContactNeighbor Y c v := ⟨w,hadj.1.symm,hadj.2⟩
  let d : ContactDart Y c := ⟨v,q⟩
  have hnot : ¬ (contactTriangleFlag hY hc d=true ∧
      contactTriangleFlag hY hc (contactReverse Y c d)=true) := by
    rintro ⟨h1,h2⟩
    have hs : (sharedTriangleGraph hY hc).Adj v w := ⟨q,rfl,h1,h2⟩
    have hp := ((sharedTriangleGraph hY hc).degree_pos_iff_exists_adj w).mpr
      ⟨v,(sharedTriangleGraph hY hc).adj_symm hs⟩
    omega
  by_cases h1 : contactTriangleFlag hY hc d=true
  · have h2 : contactTriangleFlag hY hc (contactReverse Y c d)≠true := fun h => hnot ⟨h1,h⟩
    obtain ⟨f,j,hj⟩ := nontriangle_contactDart_quad hY hc hcupper hirr hsupport _ h2
    have hb : quadFaceVertex f j=w := congrArg Sigma.fst hj
    have ht : quadFaceVertex f (j+1)=v := by
      rw [←quadFaceDart_tip]
      exact congrArg (fun e : ContactDart Y c => e.2.val) hj
    refine ⟨f,j+1,ht,Or.inr ?_⟩
    simpa only [show j+1+3=j by fin_cases j <;> decide] using hb
  · obtain ⟨f,j,hj⟩ := nontriangle_contactDart_quad hY hc hcupper hirr hsupport d h1
    refine ⟨f,j,congrArg Sigma.fst hj,Or.inl ?_⟩
    rw [←quadFaceDart_tip]
    exact congrArg (fun e : ContactDart Y c => e.2.val) hj

theorem no_shared_low_high_quad_at_center (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (v w : Fin 8) (hadj : ContactAdj Y c v w)
    (hw4 : Fintype.card (ContactNeighbor Y c w)=4)
    (htw : faceCornerCount (boundaryArray Y c hY hc 3) w≤1)
    (hothers : ∀ z,ContactAdj Y c v z → z≠w →
      Fintype.card (ContactNeighbor Y c z)=3 ∧ faceCornerCount (boundaryArray Y c hY hc 3) z=1) : False := by
  have hs0 := (sharedTriangleGraph_degree_four_cases hY hc w hw4 (by omega)).2.2 htw
  obtain ⟨f,i,hv,hw⟩ := contact_with_no_shared_edge_has_quad hY hc hcupper hirr hsupport v w hadj hs0
  have hinj := quadFaceVertex_injective f hsupport
  rcases hw with hw | hw
  · let z := quadFaceVertex f (i+3)
    have hzcontact : ContactAdj Y c v z := by
      refine ⟨?_,?_⟩
      · intro hz
        have hi := hinj (hv.trans hz)
        exact (show i≠i+3 by fin_cases i <;> decide) hi
      · rw [←hv,real_inner_comm]
        simpa only [show i+3+1=i by fin_cases i <;> decide] using quadFaceVertex_side f (i+3)
    have hzw : z≠w := by
      intro hz
      have hi := hinj (hz.trans hw.symm)
      exact (show i+3≠i+1 by fin_cases i <;> decide) hi
    have hz := hothers z hzcontact hzw
    have hD : (diagonalGraph hsupport).Adj w z := by
      refine ⟨f,i+1,hw,?_⟩
      congr 1
      fin_cases i <;> decide
    exact (diagonalGraph_no_mixed_types Y c hY hc hcupper hirr hbound hne hsupport w z hD).2.2
      ⟨hw4,by omega,hz.1,hz.2⟩
  · let z := quadFaceVertex f (i+1)
    have hzcontact : ContactAdj Y c v z := by
      refine ⟨?_,?_⟩
      · intro hz
        have hi := hinj (hv.trans hz)
        exact (show i≠i+1 by fin_cases i <;> decide) hi
      · rw [←hv]
        exact quadFaceVertex_side f i
    have hzw : z≠w := by
      intro hz
      have hi := hinj (hz.trans hw.symm)
      exact (show i+1≠i+3 by fin_cases i <;> decide) hi
    have hz := hothers z hzcontact hzw
    have hD : (diagonalGraph hsupport).Adj w z := by
      refine ⟨f,i+3,hw,?_⟩
      congr 1
      fin_cases i <;> decide
    exact (diagonalGraph_no_mixed_types Y c hY hc hcupper hirr hbound hne hsupport w z hD).2.2
      ⟨hw4,by omega,hz.1,hz.2⟩

theorem cube_k6_single_vertex_given_label (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=6) (e : Equiv.Perm (Fin 8))
    (htLabel : ∀i,faceCornerCount (boundaryArray Y c hY hc 3) (e i)=
      if i=0 then 2 else if i.val<5 then 1 else 0)
    (htriLabel : ∀i,i≠0 → i.val<5 → inner ℝ (Y (e 0)) (Y (e i))=c) : False := by
  let d := fun i => Fintype.card (ContactNeighbor Y c (e i))
  let D := diagonalGraph hsupport
  let G := actualContactGraph Y c
  have ha := covering_no_rattlers Y c hY hc hcupper hirr hbound hne hsupport
  have hd (v : Fin 8) : Fintype.card (ContactNeighbor Y c v)=3 ∨ Fintype.card (ContactNeighbor Y c v)=4 := by
    have hh := degree_degree_four Y c hY hc.1 hcupper hirr hbound v (ha v)
    rw [←contactNeighbor_card_eq] at hh
    omega
  have hcard4 : (Finset.univ.filter (fun i => d i=4)).card=2 := by
    have hh := degree_three_four_count (fun v => Fintype.card (ContactNeighbor Y c v)) hd
    have h3 : (Finset.univ.filter (fun v => Fintype.card (ContactNeighbor Y c v)=3)).card=6 := hk
    have hr := Equiv.sum_comp e (fun v => if Fintype.card (ContactNeighbor Y c v)=4 then (1:ℕ) else 0)
    simp only [Finset.card_filter] at hh h3 ⊢
    change (∑ i,if Fintype.card (ContactNeighbor Y c (e i))=4 then 1 else 0)=2
    omega
  have hd0 : d 0=4 := by
    rcases hd (e 0) with h3 | h4
    · have hh := ((rhombus_angles_assemble Y c hY hc hcupper hirr hbound hne hsupport).1 (e 0)).1 h3
      change faceCornerCount (boundaryArray Y c hY hc 3) (e 0)≤1 at hh
      rw [htLabel] at hh
      norm_num at hh
    · exact h4
  obtain ⟨y,hy0,hfour⟩ := two_degree_four_labels d hcard4 hd0
  have hdy : d y=4 := (hfour y).mpr (Or.inr rfl)
  have hthree (i : Fin 8) (hi0 : i≠0) (hiy : i≠y) : d i=3 := by
    rcases hd (e i) with h3 | h4
    · exact h3
    · exact (((hfour i).mp h4).elim hi0 hiy).elim
  have hylt : y.val<5 := by
    by_contra hnot
    have hyge : (5 : ℕ) ≤ y.val := by omega
    have hty : faceCornerCount (boundaryArray Y c hY hc 3) (e y)=0 := by
      rw [htLabel,if_neg hy0,if_neg hnot]
    have hD4 : D.degree (e y)=4 := by
      have hh := auxiliary_graphs_diagonal_degrees Y c hY hc hcupper hirr hsupport (e y)
      change D.degree (e y)+faceCornerCount (boundaryArray Y c hY hc 3) (e y)=d y at hh
      omega
    let B : Finset (Fin 8) := (Finset.univ.filter (fun i : Fin 8 => i=0 ∨ (5 : ℕ) ≤ i.val)).erase y
    have hB : B.card=3 := by
      have hfil : (Finset.univ.filter (fun i : Fin 8 => i=0 ∨ (5 : ℕ) ≤ i.val))={0,5,6,7} := by
        apply Finset.ext
        intro i
        simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
        fin_cases i <;> decide
      change ((Finset.univ.filter (fun i : Fin 8 => i=0 ∨ (5 : ℕ) ≤ i.val)).erase y).card=3
      rw [hfil]
      fin_cases y
      all_goals try norm_num [Fin.ext_iff] at hyge
      all_goals norm_num [Fin.ext_iff]
    have hsub : D.neighborFinset (e y)⊆B.image e := by
      intro z hz
      have hadj := (D.mem_neighborFinset _ _).mp hz
      let i := e.symm z
      have hiz : e i=z := e.apply_symm_apply z
      have hiy : i≠y := by
        intro hh
        have he : z=e y := hiz.symm.trans (congrArg e hh)
        exact D.irrefl (he ▸ hadj)
      have hi : i=0 ∨ (5 : ℕ) ≤ i.val := by
        by_cases hi0 : i=0
        · exact Or.inl hi0
        · by_contra hn
          have hilt : i.val<5 := by omega
          have hi3 := hthree i hi0 hiy
          have hit : faceCornerCount (boundaryArray Y c hY hc 3) (e i)=1 := by
            rw [htLabel,if_neg hi0,if_pos hilt]
          have hdadj : D.Adj (e y) (e i) := hiz.symm ▸ hadj
          exact (diagonalGraph_no_mixed_types Y c hY hc hcupper hirr hbound hne hsupport (e y) (e i) hdadj).2.2
            ⟨hdy,by omega,hi3,hit⟩
      exact Finset.mem_image.mpr ⟨i,Finset.mem_erase.mpr ⟨hiy,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩,hiz⟩
    have hh := Finset.card_le_card hsub
    rw [SimpleGraph.card_neighborFinset_eq_degree,hD4,Finset.card_image_of_injective _ e.injective,hB] at hh
    omega
  have hstar : G.neighborFinset (e 0)={e 1,e 2,e 3,e 4} := by
    apply (Finset.eq_of_subset_of_card_le ?_ ?_).symm
    · intro z hz
      have hz' : z=e 1 ∨ z=e 2 ∨ z=e 3 ∨ z=e 4 := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hz
      rcases hz' with rfl | rfl | rfl | rfl
      all_goals apply (G.mem_neighborFinset _ _).mpr
      all_goals exact ⟨e.injective.ne (by decide),htriLabel _ (by decide) (by decide)⟩
    · rw [SimpleGraph.card_neighborFinset_eq_degree,actualContactGraph_degree]
      change d 0≤_
      rw [hd0]
      norm_num [e.injective.eq_iff,Fin.ext_iff]
  have hycontact : ContactAdj Y c (e 0) (e y) := ⟨e.injective.ne hy0.symm,htriLabel y hy0 hylt⟩
  have hty : faceCornerCount (boundaryArray Y c hY hc 3) (e y)=1 := by
    rw [htLabel,if_neg hy0,if_pos hylt]
  apply no_shared_low_high_quad_at_center Y c hY hc hcupper hirr hbound hne hsupport (e 0) (e y) hycontact hdy (by omega)
  intro z hz hzy
  have hm := (G.mem_neighborFinset _ _).mpr hz
  rw [hstar] at hm
  have hm' : z=e 1 ∨ z=e 2 ∨ z=e 3 ∨ z=e 4 := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
  rcases hm' with rfl | rfl | rfl | rfl
  all_goals refine ⟨hthree _ (by decide) (fun hh => hzy (congrArg e hh)),?_⟩
  all_goals rw [htLabel];norm_num [Fin.ext_iff]

theorem cube_k6_one_shared_vertex_impossible (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=6) (f g : TriFace Y c hY hc)
    (hfg : f≠g) (v : Fin 8) : triFaceVertices f∩triFaceVertices g≠{v} := by
  intro hinter
  obtain ⟨e,hfset,hgset,hcontacts⟩ := single_vertex_triangles_labeling f g hsupport v hinter
  have he := sphere_euler_assemble Y c hY hc hcupper hirr hbound hne hsupport
  have hT : Fintype.card (TriFace Y c hY hc)=2 := by
    have hh := he.2.2.1
    rw [hk] at hh
    exact hh
  have hpair : ({f,g} : Finset (TriFace Y c hY hc))=Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ,hT,Finset.card_pair hfg]
  have hfaces (h : TriFace Y c hY hc) : h=f ∨ h=g := by
    have hm : h∈({f,g} : Finset (TriFace Y c hY hc)) := hpair ▸ Finset.mem_univ h
    simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
  apply cube_k6_single_vertex_given_label Y c hY hc hcupper hirr hbound hne hsupport hk e _ hcontacts
  intro i
  rw [triFace_pair_indicator f g hfg hfaces hsupport (e i),hfset,hgset]
  simp only [Finset.mem_insert,Finset.mem_singleton,e.injective.eq_iff]
  fin_cases i <;> norm_num [Fin.ext_iff]

#print axioms cube_k6_one_shared_vertex_impossible

#print axioms cube_k6_single_vertex_given_label

#print axioms no_shared_low_high_quad_at_center

#print axioms two_degree_four_labels
#print axioms contact_with_no_shared_edge_has_quad
end Blueprint.Thomson.Tail.Implementation
