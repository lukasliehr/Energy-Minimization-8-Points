import AllS.Units.N_GI.N_cube_k4.N_quads_alternate

set_option maxHeartbeats 3000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem nontriangle_contactDart_quad {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10) (hirr : PackingIrreducible c Y)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (d : ContactDart Y c) (hflag : contactTriangleFlag hY hc d≠true) :
    ∃ f : QuadFace Y c hY hc, ∃ i : Fin 4,quadFaceDart f i=d := by
  obtain ⟨⟨g,j⟩,heq⟩ := (cyclePartitionMap_bijective (contactFaceNext Y c hY hc)).2 d
  let C := boundaryOrbitCycle Y c hY hc g
  have hp : C.point j=d := heq
  have hlen : C.size+1=4 := by
    rcases face_lengths_length_three_four C hirr hcupper (hsupport _) with h3 | h4
    · have hh := contactTriangleFlag_orbit_point hY hc g j
      rw [hp] at hh
      change contactTriangleFlag hY hc d=decide (C.size+1=3) at hh
      rw [h3] at hh
      exact (hflag hh).elim
    · exact h4
  let f : QuadFace Y c hY hc := ⟨g,hlen⟩
  refine ⟨f,Fin.cast hlen j,?_⟩
  change C.point (Fin.cast hlen.symm (Fin.cast hlen j))=d
  have hcast : Fin.cast hlen.symm (Fin.cast hlen j)=j := Fin.ext rfl
  rw [hcast]
  exact hp

theorem equal_degree_contact_shared {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10) (hirr : PackingIrreducible c Y)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (halt : ∀ f : QuadFace Y c hY hc,∀ i,
      Fintype.card (ContactNeighbor Y c (quadFaceVertex f i))≠
        Fintype.card (ContactNeighbor Y c (quadFaceVertex f (i+1))))
    (v w : Fin 8) (hadj : ContactAdj Y c v w)
    (heq : Fintype.card (ContactNeighbor Y c v)=Fintype.card (ContactNeighbor Y c w)) :
    (sharedTriangleGraph hY hc).Adj v w := by
  have htrue (d : ContactDart Y c)
      (hh : Fintype.card (ContactNeighbor Y c d.1)=Fintype.card (ContactNeighbor Y c d.2.val)) :
      contactTriangleFlag hY hc d=true := by
    by_contra hn
    obtain ⟨f,i,rfl⟩ := nontriangle_contactDart_quad hY hc hcupper hirr hsupport d hn
    change Fintype.card (ContactNeighbor Y c (quadFaceVertex f i))=
      Fintype.card (ContactNeighbor Y c (quadFaceDart f i).2.val) at hh
    rw [quadFaceDart_tip] at hh
    exact halt f i hh
  let q : ContactNeighbor Y c v := ⟨w,hadj.1.symm,hadj.2⟩
  exact ⟨q,rfl,htrue ⟨v,q⟩ heq,htrue (contactReverse Y c ⟨v,q⟩) heq.symm⟩

theorem triangle_flag_exists {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (v : Fin 8)
    (ht : 0 < faceCornerCount (boundaryArray Y c hY hc 3) v) :
    ∃ q : ContactNeighbor Y c v,contactTriangleFlag hY hc ⟨v,q⟩=true := by
  by_contra hn
  push_neg at hn
  have hh := contactTriangleFlag_vertex_count hY hc v
  have hz : (∑ q : ContactNeighbor Y c v,if contactTriangleFlag hY hc ⟨v,q⟩ then 1 else 0)=(0:ℕ) := by
    apply Finset.sum_eq_zero
    intro q _
    simp [hn q]
  omega

theorem cube_k4_matching_s (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=4)
    (hnoE : ∀ v,Fintype.card (ContactNeighbor Y c v)=4 →
      faceCornerCount (boundaryArray Y c hY hc 3) v≠3) :
    (∀ v w,Fintype.card (ContactNeighbor Y c v)=3 → Fintype.card (ContactNeighbor Y c w)=3 →
      ¬ContactAdj Y c v w) ∧
    (∀ v,Fintype.card (ContactNeighbor Y c v)=4 → (sharedTriangleGraph hY hc).degree v=1) ∧
    (∀ v,Fintype.card (ContactNeighbor Y c v)=3 → (sharedTriangleGraph hY hc).degree v=0) := by
  let d := fun v => Fintype.card (ContactNeighbor Y c v)
  let S := sharedTriangleGraph hY hc
  have ha := covering_no_rattlers Y c hY hc hcupper hirr hbound hne hsupport
  have hd (v : Fin 8) : d v=3 ∨ d v=4 := by
    have hh := degree_degree_four Y c hY hc.1 hcupper hirr hbound v (ha v)
    rw [←contactNeighbor_card_eq] at hh
    change Fintype.card (ContactNeighbor Y c v)=3 ∨ Fintype.card (ContactNeighbor Y c v)=4
    omega
  have ht := cube_k4_types_fixed Y c hY hc hcupper hirr hbound hne hsupport hk hnoE
  have hs := auxiliary_graphs_shared_triangle_degrees Y c hY hc hcupper hirr hbound hne hsupport
  have hequal (v w : Fin 8) (hadj : ContactAdj Y c v w) (heq : d v=d w) : S.Adj v w :=
    equal_degree_contact_shared hY hc hcupper hirr hsupport
      (fun f i => (cube_k4_quads_alternate Y c hY hc hcupper hirr hbound hne hsupport hk hnoE f i).1)
      v w hadj heq
  have hHH (v w : Fin 8) (hv : d v=3) (hw : d w=3) : ¬ContactAdj Y c v w := by
    intro hadj
    have hh := (hs.2.1 v w (hequal v w hadj (hv.trans hw.symm))).1
    change d v=4 at hh
    omega
  refine ⟨hHH,?_,fun v hv => (hs.1 v).2.2 hv⟩
  intro v hv
  have htt := (ht v).2 hv
  obtain ⟨q,hq⟩ := triangle_flag_exists hY hc v (by omega)
  let e := contactFaceNext Y c hY hc ⟨v,q⟩
  have hqr : ContactAdj Y c q.val e.2.val := ⟨e.2.property.1.symm,e.2.property.2⟩
  have hvr : ContactAdj Y c v e.2.val :=
    ⟨(contactFaceNext_no_backtrack Y c hY hc hirr ⟨v,q⟩).symm,
      contactTriangleFlag_closing_contact hY hc hirr ⟨v,q⟩ hq⟩
  have hex : ∃ w,S.Adj v w := by
    rcases hd q.val with hq3 | hq4
    · rcases hd e.2.val with hr3 | hr4
      · exact (hHH q.val e.2.val hq3 hr3 hqr).elim
      · exact ⟨e.2.val,hequal v e.2.val hvr (hv.trans hr4.symm)⟩
    · exact ⟨q.val,hequal v q.val ⟨q.property.1.symm,q.property.2⟩ (hv.trans hq4.symm)⟩
  have hp := (S.degree_pos_iff_exists_adj v).mpr hex
  have hb := (hs.1 v).1
  change S.degree v≤2 at hb
  have hn : S.degree v≠2 := by
    intro hh
    exact hnoE v hv ((hs.1 v).2.1.mp hh).2
  change S.degree v=1
  omega

#print axioms nontriangle_contactDart_quad
#print axioms equal_degree_contact_shared
#print axioms cube_k4_matching_s
end Blueprint.Thomson.Tail.Implementation
