import AllS.Units.N_GI.N_cube_k2.N_no_high

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

def quadFacesAt {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (v : Fin 8) : Finset (QuadFace Y c hY hc) :=
  Finset.univ.filter (fun f => ∃ i, quadFaceVertex f i=v)

theorem quadFaceCornersAt_image_fst {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (v : Fin 8) :
    (quadFaceCornersAt (Y:=Y) (c:=c) (hY:=hY) (hc:=hc) v).image Prod.fst=quadFacesAt v := by
  apply Finset.ext
  intro f
  simp only [Finset.mem_image,quadFaceCornersAt,quadFacesAt,Finset.mem_filter,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨g,i⟩,hg,hgf⟩
    exact ⟨i,hgf ▸ hg⟩
  · rintro ⟨i,hi⟩
    exact ⟨(f,i),hi,rfl⟩

theorem quadFacesAt_card {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1}
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) (v : Fin 8) :
    (quadFacesAt (Y:=Y) (c:=c) (hY:=hY) (hc:=hc) v).card=(diagonalGraph hsupport).degree v := by
  rw [←quadFaceCornersAt_image_fst,diagonalGraph_degree_eq_corner_count hsupport v]
  apply Finset.card_image_of_injOn
  rintro ⟨f,i⟩ hi ⟨g,j⟩ hj hfg
  change f=g at hfg
  subst g
  have hvi := (Finset.mem_filter.mp hi).2
  have hvj := (Finset.mem_filter.mp hj).2
  exact Prod.ext rfl (quadFaceVertex_injective f hsupport (hvi.trans hvj.symm))

theorem cube_k2_all_four_are_equal (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=2) (v : Fin 8)
    (hv : Fintype.card (ContactNeighbor Y c v)=4) :
    faceCornerCount (boundaryArray Y c hY hc 3) v=3 := by
  have hsum := auxiliary_graphs_incidence_identity Y c hY hc hcupper hirr hbound hne hsupport
  have hH : (Finset.univ.filter (fun w => Fintype.card (ContactNeighbor Y c w)=3 ∧
      faceCornerCount (boundaryArray Y c hY hc 3) w=1)).card=0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨h3,h1⟩ := (Finset.mem_filter.mp hw).2
    have h0 := cube_k2_no_high Y c hY hc hcupper hirr hbound hne hsupport hk w h3
    omega
  change (∑ w, if Fintype.card (ContactNeighbor Y c w)=4 then
      3-faceCornerCount (boundaryArray Y c hY hc 3) w else 0)=_ at hsum
  rw [hH] at hsum
  have hle := Finset.single_le_sum (fun w (_ : w ∈ (Finset.univ : Finset (Fin 8))) =>
    Nat.zero_le (if Fintype.card (ContactNeighbor Y c w)=4 then
      3-faceCornerCount (boundaryArray Y c hY hc 3) w else 0)) (Finset.mem_univ v)
  rw [hsum,if_pos hv] at hle
  have ht : faceCornerCount (boundaryArray Y c hY hc 3) v≤3 :=
    ((rhombus_angles_assemble Y c hY hc hcupper hirr hbound hne hsupport).1 v).2 hv
  omega

theorem cube_k2_all_quads_contain_u (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=2) (v : Fin 8)
    (hv : Fintype.card (ContactNeighbor Y c v)=3) (f : QuadFace Y c hY hc) :
    ∃ i, quadFaceVertex f i=v := by
  have ht0 := cube_k2_no_high Y c hY hc hcupper hirr hbound hne hsupport hk v hv
  have hdegree := (diagonalGraph_typed_degrees Y c hY hc hcupper hirr hsupport v).2.2.2 hv ht0
  have heuler := sphere_euler_assemble Y c hY hc hcupper hirr hbound hne hsupport
  have hQ : Fintype.card (QuadFace Y c hY hc)=3 := by
    have hh := heuler.2.2.2.1
    rw [hk] at hh
    change 2*Fintype.card (QuadFace Y c hY hc)=4+2 at hh
    omega
  have heq : quadFacesAt (Y:=Y) (c:=c) (hY:=hY) (hc:=hc) v=Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ,hQ,quadFacesAt_card hsupport v,hdegree]
  have hf : f ∈ quadFacesAt (Y:=Y) (c:=c) (hY:=hY) (hc:=hc) v := by rw [heq]; exact Finset.mem_univ _
  exact (Finset.mem_filter.mp hf).2

#print axioms quadFacesAt_card
#print axioms cube_k2_all_four_are_equal
#print axioms cube_k2_all_quads_contain_u
end Blueprint.Thomson.Tail.Implementation
