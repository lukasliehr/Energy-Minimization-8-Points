import AllS.Units.N_GI.N_cube_k08.N_delete_matching

set_option maxHeartbeats 3000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

def actualNeighborEquiv (Y : Fin 8 → Point) (c : ℝ) (v : Fin 8) :
    ContactNeighbor Y c v ≃ (actualContactGraph Y c).neighborSet v where
  toFun q := ⟨q.val,q.property.1.symm,q.property.2⟩
  invFun q := ⟨q.val,q.property.1.symm,q.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def actualDartEquiv (Y : Fin 8 → Point) (c : ℝ) :
    ContactDart Y c ≃ (actualContactGraph Y c).Dart where
  toFun d := (actualContactGraph Y c).dartOfNeighborSet d.1 (actualNeighborEquiv Y c d.1 d.2)
  invFun d := ⟨d.fst,⟨d.snd,d.adj.1.symm,d.adj.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def actualCubicRotation (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hd : ∀ v, Fintype.card (ContactNeighbor Y c v)=3) :
    CubicRotationData where
  graph := actualContactGraph Y c
  order v := (Classical.choose (contactRotateAt_fin_cycle hY hc v 3 (hd v))).trans
    (actualNeighborEquiv Y c v)

theorem actualCubicRotation_rotate (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hd : ∀ v, Fintype.card (ContactNeighbor Y c v)=3)
    (v : Fin 8) (q : ContactNeighbor Y c v) :
    (actualCubicRotation Y c hY hc hd).rotateAt v (actualNeighborEquiv Y c v q)=
      actualNeighborEquiv Y c v (contactRotateAt Y c hY hc v q) := by
  let e := Classical.choose (contactRotateAt_fin_cycle hY hc v 3 (hd v))
  obtain ⟨i,rfl⟩ := e.surjective q
  have he := Classical.choose_spec (contactRotateAt_fin_cycle hY hc v 3 (hd v)) i
  change (actualCubicRotation Y c hY hc hd).rotateAt v
    ((actualCubicRotation Y c hY hc hd).order v i)=_
  rw [CubicRotationData.rotateAt_order]
  exact congrArg (actualNeighborEquiv Y c v) he.symm

theorem actualCubicRotation_rotate_inverse (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hd : ∀ v, Fintype.card (ContactNeighbor Y c v)=3)
    (v : Fin 8) (q : ContactNeighbor Y c v) :
    ((actualCubicRotation Y c hY hc hd).rotateAt v).symm (actualNeighborEquiv Y c v q)=
      actualNeighborEquiv Y c v ((contactRotateAt Y c hY hc v).symm q) := by
  apply ((actualCubicRotation Y c hY hc hd).rotateAt v).injective
  exact ((actualCubicRotation Y c hY hc hd).rotateAt v).apply_symm_apply _ |>.trans
    ((actualCubicRotation_rotate Y c hY hc hd v ((contactRotateAt Y c hY hc v).symm q)).trans
      (congrArg (actualNeighborEquiv Y c v) ((contactRotateAt Y c hY hc v).apply_symm_apply q))).symm

theorem actualCubicRotation_next (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hd : ∀ v, Fintype.card (ContactNeighbor Y c v)=3)
    (d : ContactDart Y c) :
    (actualCubicRotation Y c hY hc hd).faceNext (actualDartEquiv Y c d)=
      actualDartEquiv Y c (contactFaceNext Y c hY hc d) := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rfl
  · let q : ContactNeighbor Y c d.2.val :=
      ⟨d.1,d.2.property.1.symm,(real_inner_comm _ _).trans d.2.property.2⟩
    exact congrArg Subtype.val (actualCubicRotation_rotate_inverse Y c hY hc hd d.2.val q)

theorem quadFaceDart_next {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : QuadFace Y c hY hc) (i : Fin 4) :
    contactFaceNext Y c hY hc (quadFaceDart f i)=quadFaceDart f (i+1) := by
  let C := boundaryOrbitCycle Y c hY hc f.val
  change contactFaceNext Y c hY hc (C.point (Fin.cast f.property.symm i))=
    C.point (Fin.cast f.property.symm (i+1))
  rw [fin_cast_add_one]
  exact C.step _

theorem cube_k08_degree_three (Y : Fin 8 → Point) (c : ℝ)
    (hk : (degreeThreeVertices Y c).card=8) :
    ∀ v, Fintype.card (ContactNeighbor Y c v)=3 := by
  have hfull : degreeThreeVertices Y c=Finset.univ :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) (by simpa using hk.ge)
  intro v
  have hm : v ∈ degreeThreeVertices Y c := hfull ▸ Finset.mem_univ v
  exact (Finset.mem_filter.mp hm).2

theorem cube_k08_all_faces_four (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=8) :
    ∀ f : ContactBoundaryOrbit Y c hY hc, (boundaryOrbitCycle Y c hY hc f).size+1=4 := by
  have heuler := sphere_euler_assemble Y c hY hc hcupper hirr hbound hne hsupport
  have hT : Fintype.card (BoundaryOfLength Y c hY hc 3)=0 := by
    have hh := heuler.2.2.1
    rw [hk] at hh
    exact hh
  intro f
  rcases face_lengths_length_three_four (boundaryOrbitCycle Y c hY hc f) hirr hcupper
    (hsupport _) with h3 | h4
  · have hpos : 0 < Fintype.card (BoundaryOfLength Y c hY hc 3) :=
      Fintype.card_pos_iff.mpr ⟨⟨f,h3⟩⟩
    omega
  · exact h4

theorem every_contactDart_quad {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1)
    (hall : ∀ f : ContactBoundaryOrbit Y c hY hc, (boundaryOrbitCycle Y c hY hc f).size+1=4)
    (d : ContactDart Y c) : ∃ f : QuadFace Y c hY hc, ∃ i : Fin 4, quadFaceDart f i=d := by
  obtain ⟨⟨g,j⟩,heq⟩ := (cyclePartitionMap_bijective (contactFaceNext Y c hY hc)).2 d
  let f : QuadFace Y c hY hc := ⟨g,hall g⟩
  refine ⟨f,Fin.cast (hall g) j,?_⟩
  change (boundaryOrbitCycle Y c hY hc g).point (Fin.cast (hall g).symm (Fin.cast (hall g) j))=d
  have hcast : Fin.cast (hall g).symm (Fin.cast (hall g) j)=j := Fin.ext rfl
  rw [hcast]
  exact heq

def actualCubicQuad (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (hd : ∀ v, Fintype.card (ContactNeighbor Y c v)=3)
    (hall : ∀ f : ContactBoundaryOrbit Y c hY hc, (boundaryOrbitCycle Y c hY hc f).size+1=4) :
    CubicQuadData where
  toCubicRotationData := actualCubicRotation Y c hY hc hd
  face_four := by
    intro d
    obtain ⟨d,rfl⟩ := (actualDartEquiv Y c).surjective d
    obtain ⟨f,i,rfl⟩ := every_contactDart_quad hY hc hall d
    rw [actualCubicRotation_next,quadFaceDart_next,actualCubicRotation_next,quadFaceDart_next,
      actualCubicRotation_next,quadFaceDart_next,actualCubicRotation_next,quadFaceDart_next]
    congr 2
    fin_cases i <;> decide
  opposite_distinct := by
    intro d
    obtain ⟨d,rfl⟩ := (actualDartEquiv Y c).surjective d
    obtain ⟨f,i,rfl⟩ := every_contactDart_quad hY hc hall d
    rw [actualCubicRotation_next,quadFaceDart_next]
    change (quadFaceDart f i).1≠(quadFaceDart f (i+1)).2.val
    rw [quadFaceDart_fst,quadFaceDart_tip]
    intro he
    have hh := quadFaceVertex_injective f hsupport he
    have hn : ∀ i : Fin 4, i≠i+1+1 := by decide
    exact hn i hh
  opposite_nonadjacent := by
    intro d
    obtain ⟨d,rfl⟩ := (actualDartEquiv Y c).surjective d
    obtain ⟨f,i,rfl⟩ := every_contactDart_quad hY hc hall d
    rw [actualCubicRotation_next,quadFaceDart_next]
    change ¬ContactAdj Y c (quadFaceDart f i).1 (quadFaceDart f (i+1)).2.val
    rw [quadFaceDart_fst,quadFaceDart_tip]
    intro h
    have hlt := auxiliary_graphs_diagonal_noncontact f hirr hbound hsupport i
    rw [show i+1+1=i+2 by fin_cases i <;> decide] at h
    exact hlt.ne h.2

theorem cube_k08_all_cubic (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=8) :
    HasSpanningCube (actualContactGraph Y c) := by
  let Q := actualCubicQuad Y c hY hc hirr hbound hsupport (cube_k08_degree_three Y c hk)
    (cube_k08_all_faces_four Y c hY hc hcupper hirr hbound hne hsupport hk)
  exact cubic_quads_cube_labeling Q

theorem cube_k08_all_cubic_exact (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=8) :
    ∃ e : CubeVertex ≃ Fin 8, ∀u v : CubeVertex,
      (actualContactGraph Y c).Adj (e u) (e v) ↔ u.1≠v.1 ∧ u.2≠v.2 := by
  let Q := actualCubicQuad Y c hY hc hirr hbound hsupport (cube_k08_degree_three Y c hk)
    (cube_k08_all_faces_four Y c hY hc hcupper hirr hbound hne hsupport hk)
  exact cubic_quads_assemble Q

#print axioms cube_k08_all_cubic_exact

#print axioms cube_k08_all_cubic
#print axioms actualCubicRotation_next
#print axioms quadFaceDart_next
#print axioms cube_k08_degree_three
end Blueprint.Thomson.Tail.Implementation
