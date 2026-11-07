import AllS.Units.N_GI.N_auxiliary_graphs.N_diagonal_simple
import AllS.Units.N_GI.N_rhombus_angles.N_assemble
import Mathlib.Combinatorics.SimpleGraph.Finite

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

def DiagonalAdj {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (v w : Fin 8) : Prop :=
  ∃ f : QuadFace Y c hY hc, ∃ i : Fin 4,
    quadFaceVertex f i=v ∧ quadFaceVertex f (i+2)=w

def diagonalGraph {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1}
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) : SimpleGraph (Fin 8) where
  Adj := DiagonalAdj (Y:=Y) (c:=c) (hY:=hY) (hc:=hc)
  symm := ⟨by
    rintro v w ⟨f,i,hv,hw⟩
    refine ⟨f,i+2,hw,?_⟩
    simpa only [show i+2+2=i by fin_cases i <;> decide] using hv⟩
  loopless := ⟨by
    rintro v ⟨f,i,hv,hw⟩
    have hi := quadFaceVertex_injective f hsupport (hv.trans hw.symm)
    have hh : i≠i+2 := by fin_cases i <;> decide
    exact hh hi⟩

def quadFaceCornersAt {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (v : Fin 8) : Finset (QuadFace Y c hY hc × Fin 4) := by
  classical
  exact Finset.univ.filter (fun p => quadFaceVertex p.1 p.2=v)

theorem diagonalNeighborFinset_eq {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1}
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) (v : Fin 8) :
    (diagonalGraph hsupport).neighborFinset v =
      (quadFaceCornersAt (Y:=Y) (c:=c) (hY:=hY) (hc:=hc) v).image
        (fun p => quadFaceVertex p.1 (p.2+2)) := by
  classical
  apply Finset.ext
  intro w
  rw [SimpleGraph.mem_neighborFinset]
  change DiagonalAdj v w ↔ _
  simp only [DiagonalAdj, Finset.mem_image,
    quadFaceCornersAt, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨f,i,hv,hw⟩
    exact ⟨(f,i),hv,hw⟩
  · rintro ⟨⟨f,i⟩,hv,hw⟩
    exact ⟨f,i,hv,hw⟩

theorem diagonalGraph_degree_eq_corner_count {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1}
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) (v : Fin 8) :
    (diagonalGraph hsupport).degree v =
      (quadFaceCornersAt (Y:=Y) (c:=c) (hY:=hY) (hc:=hc) v).card := by
  classical
  rw [SimpleGraph.degree,diagonalNeighborFinset_eq]
  apply Finset.card_image_of_injOn
  rintro ⟨f,i⟩ hf ⟨g,j⟩ hg heq
  have hfv : quadFaceVertex f i=v := (Finset.mem_filter.mp hf).2
  have hgv : quadFaceVertex g j=v := (Finset.mem_filter.mp hg).2
  have h := auxiliary_graphs_diagonal_simple f g hsupport i j (hfv.trans hgv.symm) heq
  exact Prod.ext h.1 h.2

theorem quadFaceCornersAt_card {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (v : Fin 8) :
    (quadFaceCornersAt (Y:=Y) (c:=c) (hY:=hY) (hc:=hc) v).card =
      faceCornerCount (boundaryArray Y c hY hc 4) v := by
  classical
  simp only [quadFaceCornersAt,faceCornerCount,faceCornersAt,Finset.card_filter,Fintype.sum_prod_type]
  exact (Equiv.sum_comp (Fintype.equivFin (QuadFace Y c hY hc)).symm
    (fun f => ∑ j : Fin 4, if quadFaceVertex f j=v then (1:ℕ) else 0)).symm

theorem auxiliary_graphs_diagonal_degrees (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10) (hirr : PackingIrreducible c Y)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) (v : Fin 8) :
    (diagonalGraph hsupport).degree v + faceCornerCount (boundaryArray Y c hY hc 3) v =
      Fintype.card (ContactNeighbor Y c v) := by
  rw [diagonalGraph_degree_eq_corner_count hsupport v,quadFaceCornersAt_card,add_comm]
  exact tiling_data_vertex_incidence Y c hY hc hcupper hirr hsupport v

theorem diagonalGraph_noncontact {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) (v w : Fin 8)
    (hvw : (diagonalGraph hsupport).Adj v w) : inner ℝ (Y v) (Y w)<c := by
  obtain ⟨f,i,rfl,rfl⟩ := hvw
  exact auxiliary_graphs_diagonal_noncontact f hirr hbound hsupport i


theorem diagonalGraph_typed_degrees (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10) (hirr : PackingIrreducible c Y)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) (v : Fin 8) :
    let d := Fintype.card (ContactNeighbor Y c v)
    let t := faceCornerCount (boundaryArray Y c hY hc 3) v
    (d=4 → t=3 → (diagonalGraph hsupport).degree v=1) ∧
    (d=4 → t≤2 → (diagonalGraph hsupport).degree v=4-t) ∧
    (d=3 → t=1 → (diagonalGraph hsupport).degree v=2) ∧
    (d=3 → t=0 → (diagonalGraph hsupport).degree v=3) := by
  have h := auxiliary_graphs_diagonal_degrees Y c hY hc hcupper hirr hsupport v
  dsimp only
  omega

theorem diagonalGraph_no_mixed_types (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10) (hirr : PackingIrreducible c Y)
    (hbound : PackingInnerBound c Y) (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) (v w : Fin 8)
    (hvw : (diagonalGraph hsupport).Adj v w) :
    let d := fun x => Fintype.card (ContactNeighbor Y c x)
    let t := faceCornerCount (boundaryArray Y c hY hc 3)
    ¬ (d v=4 ∧ t v=3 ∧ d w=4 ∧ t w≤2) ∧
    ¬ (d v=4 ∧ t v=3 ∧ d w=3 ∧ t w=1) ∧
    ¬ (d v=4 ∧ t v≤2 ∧ d w=3 ∧ t w=1) := by
  dsimp only
  obtain ⟨f,i,rfl,rfl⟩ := hvw
  let D := tiling_data_construct_existing_data Y c hY hc hcupper hirr hbound hne hsupport
  let f' : Fin D.quadCount := (Fintype.equivFin (QuadFace Y c hY hc)) f
  have hvert (j : Fin 4) : D.quad f' j = quadFaceVertex f j :=
    boundaryArray_ofLength Y c hY hc 4 f j
  have hleft := (rhombus_angles_assemble Y c hY hc hcupper hirr hbound hne hsupport).2 f' i
  have hright := (rhombus_angles_assemble Y c hY hc hcupper hirr hbound hne hsupport).2 f' (i+2)
  change (_ → _ → D.angle f' i=D.beta) ∧ (_ → _ → D.angle f' i<D.beta) ∧
    (_ → _ → D.beta<D.angle f' i) at hleft
  change (_ → _ → D.angle f' (i+2)=D.beta) ∧ (_ → _ → D.angle f' (i+2)<D.beta) ∧
    (_ → _ → D.beta<D.angle f' (i+2)) at hright
  have hd (j : Fin 4) : Fintype.card (ContactNeighbor Y c (D.quad f' j)) =
      Fintype.card (ContactNeighbor Y c (quadFaceVertex f j)) :=
    congrArg (fun v => Fintype.card (ContactNeighbor Y c v)) (hvert j)
  have ht (j : Fin 4) : faceCornerCount D.tri (D.quad f' j) =
      faceCornerCount (boundaryArray Y c hY hc 3) (quadFaceVertex f j) :=
    congrArg (faceCornerCount D.tri) (hvert j)
  have hang : D.angle f' (i+2)=D.angle f' i :=
    rhombus_angles_opposite c (fun j => Y (D.quad f' j)) i
  refine ⟨?_,?_,?_⟩
  · rintro ⟨hdv,htv,hdw,htw⟩
    have h1 := hleft.1 ((hd i).trans hdv) ((ht i).trans htv)
    have h2 := hright.2.1 ((hd (i+2)).trans hdw) (le_of_eq_of_le (ht (i+2)) htw)
    linarith
  · rintro ⟨hdv,htv,hdw,htw⟩
    have h1 := hleft.1 ((hd i).trans hdv) ((ht i).trans htv)
    have h2 := hright.2.2 ((hd (i+2)).trans hdw) ((ht (i+2)).trans htw)
    linarith
  · rintro ⟨hdv,htv,hdw,htw⟩
    have h1 := hleft.2.1 ((hd i).trans hdv) (le_of_eq_of_le (ht i) htv)
    have h2 := hright.2.2 ((hd (i+2)).trans hdw) ((ht (i+2)).trans htw)
    linarith

#print axioms diagonalGraph_typed_degrees
#print axioms diagonalGraph_no_mixed_types

#print axioms auxiliary_graphs_diagonal_degrees
#print axioms diagonalGraph_noncontact
end Blueprint.Thomson.Tail.Implementation
