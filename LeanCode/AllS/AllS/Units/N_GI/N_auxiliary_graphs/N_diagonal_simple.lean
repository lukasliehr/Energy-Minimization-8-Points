import AllS.Units.N_GI.N_tiling_data.N_face_arrays
import Lean_Code.RhombusOrientation

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

/-- The rank-three Gram identity proves that the two distinct known common
neighbors exhaust the intersection of the two contact circles. -/
theorem common_contact_neighbors_exhaust (a b d e z : Point) (c : ℝ)
    (ha : ‖a‖=1) (hb : ‖b‖=1) (hd : ‖d‖=1) (he : ‖e‖=1) (hz : ‖z‖=1)
    (hc : 0<c) (had : a≠d) (hbe : b≠e)
    (hab : inner ℝ a b=c) (hdb : inner ℝ d b=c)
    (hae : inner ℝ a e=c) (hde : inner ℝ d e=c)
    (haz : inner ℝ a z=c) (hdz : inner ℝ d z=c) : z=b ∨ z=e := by
  by_cases hzb : z=b
  · exact Or.inl hzb
  have hbd : inner ℝ b d=c := (real_inner_comm d b).trans hdb
  have hea : inner ℝ e a=c := (real_inner_comm a e).trans hae
  have hza : inner ℝ z a=c := (real_inner_comm a z).trans haz
  let Q : Fin 4 → Point := ![a,b,d,e]
  have hQ : ∀ i, ‖Q i‖=1 := by intro i; fin_cases i <;> simp [Q,ha,hb,hd,he]
  have hgram := rhombus_diagonal_identity Q c hQ had hbe hab hbd hde hea
  change (1+inner ℝ a d)*(1+inner ℝ b e)=4*c^2 at hgram
  have hn : 1+inner ℝ a d ≠ 0 := by
    intro h
    rw [h,zero_mul] at hgram
    nlinarith [sq_pos_of_pos hc]
  have h1 := contact_rhombus_sum_relation a b d e c ha hb hd he had hbe hab hbd hde hea
  have h2 := contact_rhombus_sum_relation a b d z c ha hb hd hz had (Ne.symm hzb) hab hbd hdz hza
  have hsame := congrArg (fun w : Point => (1+inner ℝ a d)⁻¹ • w) (h2.trans h1.symm)
  simp only [smul_smul, inv_mul_cancel₀ hn, one_smul] at hsame
  exact Or.inr (add_left_cancel hsame)

theorem auxiliary_graphs_diagonal_neighbors (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : 0<c) (v : Fin 4 → Fin 8)
    (hinj : Function.Injective v) (hside : ∀ j, inner ℝ (Y (v j)) (Y (v (j+1)))=c)
    (z : Fin 8) (hz0 : inner ℝ (Y (v 0)) (Y z)=c) (hz2 : inner ℝ (Y (v 2)) (Y z)=c) :
    z=v 1 ∨ z=v 3 := by
  have h02 : Y (v 0) ≠ Y (v 2) := fun h => (by decide : (0:Fin 4)≠2) (hinj (hY.2 h))
  have h13 : Y (v 1) ≠ Y (v 3) := fun h => (by decide : (1:Fin 4)≠3) (hinj (hY.2 h))
  have h21 : inner ℝ (Y (v 2)) (Y (v 1))=c := (real_inner_comm _ _).trans (hside 1)
  have h03 : inner ℝ (Y (v 0)) (Y (v 3))=c := (real_inner_comm _ _).trans (hside 3)
  rcases common_contact_neighbors_exhaust (Y (v 0)) (Y (v 1)) (Y (v 2)) (Y (v 3)) (Y z) c
    (hY.1 _) (hY.1 _) (hY.1 _) (hY.1 _) (hY.1 _) hc h02 h13
    (hside 0) h21 h03 (hside 2) hz0 hz2 with h | h
  · exact Or.inl (hY.2 h)
  · exact Or.inr (hY.2 h)

#print axioms common_contact_neighbors_exhaust
#print axioms auxiliary_graphs_diagonal_neighbors
abbrev QuadFace (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) := BoundaryOfLength Y c hY hc 4

def quadFaceVertex {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : QuadFace Y c hY hc) (i : Fin 4) : Fin 8 :=
  (boundaryOrbitCycle Y c hY hc f.val).reindex f.property i

def quadFaceDart {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : QuadFace Y c hY hc) (i : Fin 4) : ContactDart Y c :=
  (boundaryOrbitCycle Y c hY hc f.val).point (Fin.cast f.property.symm i)

theorem quadFaceVertex_injective {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : QuadFace Y c hY hc)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) :
    Function.Injective (quadFaceVertex f) :=
  (boundaryOrbitCycle Y c hY hc f.val).reindex_injective f.property (hsupport _)

theorem quadFaceVertex_side {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : QuadFace Y c hY hc) (i : Fin 4) :
    inner ℝ (Y (quadFaceVertex f i)) (Y (quadFaceVertex f (i+1)))=c :=
  (boundaryOrbitCycle Y c hY hc f.val).reindex_side f.property i

theorem quadFaceVertex_corner_orientation {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : QuadFace Y c hY hc)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) (i : Fin 4) :
    0 < inner ℝ (crossVec (Y (quadFaceVertex f i)) (Y (quadFaceVertex f (i+1))))
      (Y (quadFaceVertex f (i+3))) := by
  let Q := face_lengths_polygon (n := 1) (boundaryOrbitCycle Y c hY hc f.val) f.property (hsupport _)
  exact Q.support i (i+3) (by fin_cases i <;> decide) (by fin_cases i <;> decide)

theorem quadFaceDart_fst {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : QuadFace Y c hY hc) (i : Fin 4) :
    (quadFaceDart f i).1=quadFaceVertex f i := rfl

theorem quadFaceDart_tip {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : QuadFace Y c hY hc) (i : Fin 4) :
    (quadFaceDart f i).2.val=quadFaceVertex f (i+1) := by
  let C := boundaryOrbitCycle Y c hY hc f.val
  change (C.point (Fin.cast f.property.symm i)).2.val=C.vertex (Fin.cast f.property.symm (i+1))
  rw [fin_cast_add_one]
  exact (C.vertex_next _).symm

theorem quadFaceDart_class {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : QuadFace Y c hY hc) (i : Fin 4) :
    (Quotient.mk (permutationOrbitSetoid (contactFaceNext Y c hY hc)) (quadFaceDart f i)) = f.val :=
  orbitPermutationCycle_class (contactFaceNext Y c hY hc) f.val (Fin.cast f.property.symm i)

theorem quadFace_common_neighbors {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : QuadFace Y c hY hc)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (i : Fin 4) (z : Fin 8)
    (h0 : inner ℝ (Y (quadFaceVertex f i)) (Y z)=c)
    (h2 : inner ℝ (Y (quadFaceVertex f (i+2))) (Y z)=c) :
    z=quadFaceVertex f (i+1) ∨ z=quadFaceVertex f (i+3) := by
  have hinj : Function.Injective (fun k => quadFaceVertex f (i+k)) := by
    intro a b hab
    exact add_left_cancel (quadFaceVertex_injective f hsupport hab)
  have hside (k : Fin 4) : inner ℝ (Y (quadFaceVertex f (i+k)))
      (Y (quadFaceVertex f (i+(k+1))))=c := by
    simpa only [add_assoc] using quadFaceVertex_side f (i+k)
  exact auxiliary_graphs_diagonal_neighbors Y c hY hc.1
    (fun k => quadFaceVertex f (i+k)) hinj hside z (by simpa using h0) h2

#print axioms quadFace_common_neighbors

theorem quadFace_opposite_next_contact {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : QuadFace Y c hY hc) (i : Fin 4) :
    inner ℝ (Y (quadFaceVertex f (i+2))) (Y (quadFaceVertex f (i+1)))=c := by
  have h := quadFaceVertex_side f (i+1)
  rw [show i+1+1=i+2 by fin_cases i <;> decide] at h
  exact (real_inner_comm _ _).trans h

theorem quadFace_previous_contacts {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : QuadFace Y c hY hc) (i : Fin 4) :
    inner ℝ (Y (quadFaceVertex f i)) (Y (quadFaceVertex f (i+3)))=c ∧
      inner ℝ (Y (quadFaceVertex f (i+2))) (Y (quadFaceVertex f (i+3)))=c := by
  constructor
  · have h := quadFaceVertex_side f (i+3)
    rw [show i+3+1=i by fin_cases i <;> decide] at h
    exact (real_inner_comm _ _).trans h
  · simpa only [show i+2+1=i+3 by fin_cases i <;> decide] using quadFaceVertex_side f (i+2)

theorem actual_contactDart_ext {Y : Fin 8 → Point} {c : ℝ} (d e : ContactDart Y c)
    (hb : d.1=e.1) (ht : d.2.val=e.2.val) : d=e := by
  rcases d with ⟨u,a⟩
  rcases e with ⟨v,b⟩
  dsimp only at hb ht
  subst v
  have hab : a=b := Subtype.ext ht
  rw [hab]

theorem auxiliary_graphs_diagonal_simple {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f g : QuadFace Y c hY hc)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (i j : Fin 4) (hbase : quadFaceVertex f i=quadFaceVertex g j)
    (hop : quadFaceVertex f (i+2)=quadFaceVertex g (j+2)) : f=g ∧ i=j := by
  have hn := quadFace_common_neighbors f hsupport i (quadFaceVertex g (j+1))
    (by rw [hbase]; exact quadFaceVertex_side g j)
    (by rw [hop]; exact quadFace_opposite_next_contact g j)
  have hp := quadFace_common_neighbors f hsupport i (quadFaceVertex g (j+3))
    (by rw [hbase]; exact (quadFace_previous_contacts g j).1)
    (by rw [hop]; exact (quadFace_previous_contacts g j).2)
  have hne : quadFaceVertex g (j+1) ≠ quadFaceVertex g (j+3) := by
    intro h
    have hh := quadFaceVertex_injective g hsupport h
    have hbad : j+1 ≠ j+3 := by fin_cases j <;> decide
    exact hbad hh
  have hnext : quadFaceVertex g (j+1)=quadFaceVertex f (i+1) := by
    rcases hn with hn | hn
    · exact hn
    · rcases hp with hp | hp
      · have hg := quadFaceVertex_corner_orientation g hsupport j
        have hf := quadFaceVertex_corner_orientation f hsupport i
        rw [←hbase,hn,hp] at hg
        rw [triple_swap_last] at hg
        linarith
      · exact False.elim (hne (hn.trans hp.symm))
  have hd : quadFaceDart f i=quadFaceDart g j := by
    exact actual_contactDart_ext _ _ hbase
      ((quadFaceDart_tip f i).trans (hnext.symm.trans (quadFaceDart_tip g j).symm))
  have hfge : f=g := by
    apply Subtype.ext
    exact (quadFaceDart_class f i).symm.trans
      ((congrArg (Quotient.mk (permutationOrbitSetoid (contactFaceNext Y c hY hc))) hd).trans
        (quadFaceDart_class g j))
  refine ⟨hfge, ?_⟩
  subst g
  exact quadFaceVertex_injective f hsupport hbase

#print axioms auxiliary_graphs_diagonal_simple

theorem auxiliary_graphs_diagonal_noncontact {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : QuadFace Y c hY hc)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) (i : Fin 4) :
    inner ℝ (Y (quadFaceVertex f i)) (Y (quadFaceVertex f (i+2))) < c := by
  exact (boundaryOrbitCycle Y c hY hc f.val).reindex_diagonal f.property hirr hbound
    (hsupport _) i (i+2) (by fin_cases i <;> decide)
    (by fin_cases i <;> decide) (by fin_cases i <;> decide)

#print axioms auxiliary_graphs_diagonal_noncontact

end Blueprint.Thomson.Tail.Implementation
