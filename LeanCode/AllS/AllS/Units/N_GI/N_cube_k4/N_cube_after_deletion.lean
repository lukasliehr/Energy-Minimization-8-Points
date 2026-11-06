import AllS.Units.N_GI.N_matching_delete.N_shared_edges

set_option maxHeartbeats 700000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem cube_k4_cube_after_deletion (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=4)
    (hnoE : ∀ v,Fintype.card (ContactNeighbor Y c v)=4 →
      faceCornerCount (boundaryArray Y c hY hc 3) v≠3) :
    HasSpanningCube (actualContactGraph Y c) := by
  let S := sharedTriangleGraph hY hc
  let d := fun v => Fintype.card (ContactNeighbor Y c v)
  have ha := covering_no_rattlers Y c hY hc hcupper hirr hbound hne hsupport
  have hd (z : Fin 8) : d z=3 ∨ d z=4 := by
    have hh := degree_degree_four Y c hY hc.1 hcupper hirr hbound z (ha z)
    rw [←contactNeighbor_card_eq] at hh
    change Fintype.card (ContactNeighbor Y c z)=3 ∨ Fintype.card (ContactNeighbor Y c z)=4
    omega
  have hm := cube_k4_matching_s Y c hY hc hcupper hirr hbound hne hsupport hk hnoE
  have hSdegree (v : Fin 8) : S.degree v+3=d v := by
    rcases hd v with h3 | h4
    · have hz := hm.2.2 v h3
      change S.degree v=0 at hz
      omega
    · have hz := hm.2.1 v h4
      change S.degree v=1 at hz
      omega
  have hside (f : TriFace Y c hY hc) : ∃i : Fin 3,S.Adj (triFaceVertex f i) (triFaceVertex f (i+1)) := by
    have hadj (i j : Fin 3) (hij : i≠j) : ContactAdj Y c (triFaceVertex f i) (triFaceVertex f j) :=
      ⟨fun h => hij (triFaceVertex_injective f hsupport h),triFaceVertex_contact f i j hij⟩
    have heq (i j : Fin 3) (hij : i≠j) (hi : d (triFaceVertex f i)=4) (hj : d (triFaceVertex f j)=4) :
        S.Adj (triFaceVertex f i) (triFaceVertex f j) :=
      equal_degree_contact_shared hY hc hcupper hirr hsupport
        (fun g k => (cube_k4_quads_alternate Y c hY hc hcupper hirr hbound hne hsupport hk hnoE g k).1)
        _ _ (hadj i j hij) (hi.trans hj.symm)
    rcases hd (triFaceVertex f 0) with h03 | h04
    · rcases hd (triFaceVertex f 1) with h13 | h14
      · exact (hm.1 _ _ h03 h13 (hadj 0 1 (by decide))).elim
      · rcases hd (triFaceVertex f 2) with h23 | h24
        · exact (hm.1 _ _ h03 h23 (hadj 0 2 (by decide))).elim
        · exact ⟨1,heq 1 2 (by decide) h14 h24⟩
    · rcases hd (triFaceVertex f 1) with h13 | h14
      · rcases hd (triFaceVertex f 2) with h23 | h24
        · exact (hm.1 _ _ h13 h23 (hadj 1 2 (by decide))).elim
        · exact ⟨2,heq 2 0 (by decide) h24 h04⟩
      · exact ⟨0,heq 0 1 (by decide) h04 h14⟩
  exact matching_delete_spanning_cube hY hc hcupper hirr hbound hsupport S
    (sharedTriangleGraph_subgraph hY hc) hd hSdegree
    (sharedTriangleGraph_flag hY hc) (triangle_deletion_from_face_sides hY hc S hside)

#print axioms cube_k4_cube_after_deletion
end Blueprint.Thomson.Tail.Implementation
