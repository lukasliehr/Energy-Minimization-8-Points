import AllS.Units.N_GI.N_cube_k4.N_matching_s

set_option maxHeartbeats 3000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

abbrev TriFace (Y : Fin 8 → Point) (c : ℝ) (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) := BoundaryOfLength Y c hY hc 3

def triFaceVertex {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : TriFace Y c hY hc) (i : Fin 3) : Fin 8 :=
  (boundaryOrbitCycle Y c hY hc f.val).reindex f.property i

def triFaceDart {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : TriFace Y c hY hc) (i : Fin 3) : ContactDart Y c :=
  (boundaryOrbitCycle Y c hY hc f.val).point (Fin.cast f.property.symm i)

theorem triFaceVertex_injective {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : TriFace Y c hY hc)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport) :
    Function.Injective (triFaceVertex f) :=
  (boundaryOrbitCycle Y c hY hc f.val).reindex_injective f.property (hsupport _)

theorem triFaceVertex_contact {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : TriFace Y c hY hc) (i j : Fin 3) (hij : i≠j) :
    inner ℝ (Y (triFaceVertex f i)) (Y (triFaceVertex f j))=c :=
  (boundaryOrbitCycle Y c hY hc f.val).reindex_triangle_contacts f.property i j hij

theorem triFaceDart_tip {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : TriFace Y c hY hc) (i : Fin 3) :
    (triFaceDart f i).2.val=triFaceVertex f (i+1) := by
  let C := boundaryOrbitCycle Y c hY hc f.val
  change (C.point (Fin.cast f.property.symm i)).2.val=C.vertex (Fin.cast f.property.symm (i+1))
  rw [fin_cast_add_one]
  exact (C.vertex_next _).symm

theorem triFaceDart_class {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : TriFace Y c hY hc) (i : Fin 3) :
    contactFaceKey hY hc (triFaceDart f i)=f.val :=
  orbitPermutationCycle_class (contactFaceNext Y c hY hc) f.val (Fin.cast f.property.symm i)

theorem triFaceVertex_turn {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : TriFace Y c hY hc) (hirr : PackingIrreducible c Y)
    (i : Fin 3) : 0 < inner ℝ (crossVec (Y (triFaceVertex f i)) (Y (triFaceVertex f (i+1))))
      (Y (triFaceVertex f (i+2))) := by
  let C := boundaryOrbitCycle Y c hY hc f.val
  have hh := C.strict_turn hirr (Fin.cast f.property.symm i)
  change 0 < inner ℝ (crossVec (Y (C.vertex (Fin.cast f.property.symm i)))
    (Y (C.vertex (Fin.cast f.property.symm (i+1))))) (Y (C.vertex (Fin.cast f.property.symm (i+2))))
  rw [fin_cast_add_one,show i+2=i+1+1 by fin_cases i <;> decide,fin_cast_add_one,fin_cast_add_one]
  exact hh

def triFaceVertices {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : TriFace Y c hY hc) : Finset (Fin 8) :=
  Finset.univ.image (triFaceVertex f)

theorem triFaceVertices_card {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : TriFace Y c hY hc)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport) :
    (triFaceVertices f).card=3 := by
  rw [triFaceVertices,Finset.card_image_of_injective _ (triFaceVertex_injective f hsupport),
    Finset.card_univ,Fintype.card_fin]

theorem triFace_oriented_edge_unique {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f g : TriFace Y c hY hc) (i j : Fin 3)
    (h0 : triFaceVertex f i=triFaceVertex g j)
    (h1 : triFaceVertex f (i+1)=triFaceVertex g (j+1)) : f=g := by
  have he : triFaceDart f i=triFaceDart g j := actual_contactDart_ext _ _ h0
    ((triFaceDart_tip f i).trans (h1.trans (triFaceDart_tip g j).symm))
  exact Subtype.ext ((triFaceDart_class f i).symm.trans
    ((congrArg (contactFaceKey hY hc) he).trans (triFaceDart_class g j)))

theorem triFaceVertices_injective {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (hirr : PackingIrreducible c Y)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport) :
    Function.Injective (triFaceVertices (Y:=Y) (c:=c) (hY:=hY) (hc:=hc)) := by
  intro f g heq
  have hex (i : Fin 3) : ∃ j : Fin 3,triFaceVertex g j=triFaceVertex f i := by
    have hm : triFaceVertex f i ∈ triFaceVertices g := heq ▸ Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hm
    exact ⟨j,hj⟩
  obtain ⟨j,hj⟩ := hex 0
  obtain ⟨k,hk⟩ := hex 1
  obtain ⟨l,hl⟩ := hex 2
  have hjk : j≠k := fun h => (by decide : (0:Fin 3)≠1)
    (triFaceVertex_injective f hsupport (hj.symm.trans ((congrArg (triFaceVertex g) h).trans hk)))
  have hjl : j≠l := fun h => (by decide : (0:Fin 3)≠2)
    (triFaceVertex_injective f hsupport (hj.symm.trans ((congrArg (triFaceVertex g) h).trans hl)))
  have hkl : k≠l := fun h => (by decide : (1:Fin 3)≠2)
    (triFaceVertex_injective f hsupport (hk.symm.trans ((congrArg (triFaceVertex g) h).trans hl)))
  have hcases : (k=j+1 ∧ l=j+2) ∨ (k=j+2 ∧ l=j+1) := by
    have hh : ∀ j k l : Fin 3,j≠k → j≠l → k≠l →
      ((k=j+1 ∧ l=j+2) ∨ (k=j+2 ∧ l=j+1)) := by decide
    exact hh j k l hjk hjl hkl
  rcases hcases with ⟨hkpos,hlpos⟩ | ⟨hkneg,hlneg⟩
  · apply triFace_oriented_edge_unique f g 0 j hj.symm
    rw [←hkpos]
    exact hk.symm
  · have hf := triFaceVertex_turn f hirr 0
    have hg := triFaceVertex_turn g hirr j
    change 0 < inner ℝ (crossVec (Y (triFaceVertex f 0)) (Y (triFaceVertex f 1)))
      (Y (triFaceVertex f 2)) at hf
    rw [←hj,←hk,←hl,hkneg,hlneg,triple_swap_last] at hf
    linarith

def triFacesAt {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (v : Fin 8) : Finset (TriFace Y c hY hc) :=
  Finset.univ.filter (fun f => ∃ i,triFaceVertex f i=v)

def triFaceCornersAt {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (v : Fin 8) : Finset (TriFace Y c hY hc × Fin 3) :=
  Finset.univ.filter (fun p => triFaceVertex p.1 p.2=v)

theorem triFaceCornersAt_card {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (v : Fin 8) :
    (triFaceCornersAt (Y:=Y) (c:=c) (hY:=hY) (hc:=hc) v).card=
      faceCornerCount (boundaryArray Y c hY hc 3) v := by
  simp only [triFaceCornersAt,faceCornerCount,faceCornersAt,Finset.card_filter,Fintype.sum_prod_type]
  exact (Equiv.sum_comp (Fintype.equivFin (TriFace Y c hY hc)).symm
    (fun f => ∑ j : Fin 3,if triFaceVertex f j=v then (1:ℕ) else 0)).symm

theorem triFaceCornersAt_image_fst {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (v : Fin 8) :
    (triFaceCornersAt (Y:=Y) (c:=c) (hY:=hY) (hc:=hc) v).image Prod.fst=triFacesAt v := by
  apply Finset.ext
  intro f
  simp only [Finset.mem_image,triFaceCornersAt,triFacesAt,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨⟨g,i⟩,hi,hgf⟩
    exact ⟨i,hgf ▸ hi⟩
  · rintro ⟨i,hi⟩
    exact ⟨(f,i),hi,rfl⟩

theorem triFacesAt_card {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1}
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport) (v : Fin 8) :
    (triFacesAt (Y:=Y) (c:=c) (hY:=hY) (hc:=hc) v).card=
      faceCornerCount (boundaryArray Y c hY hc 3) v := by
  rw [←triFaceCornersAt_image_fst,←triFaceCornersAt_card]
  apply Finset.card_image_of_injOn
  rintro ⟨f,i⟩ hi ⟨g,j⟩ hj hfg
  change f=g at hfg
  subst g
  have hvi := (Finset.mem_filter.mp hi).2
  have hvj := (Finset.mem_filter.mp hj).2
  exact Prod.ext rfl (triFaceVertex_injective f hsupport (hvi.trans hvj.symm))

theorem triangle_incidence_indicator {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1}
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport) (v : Fin 8) :
    faceCornerCount (boundaryArray Y c hY hc 3) v=
      ∑ f : TriFace Y c hY hc,if v∈triFaceVertices f then 1 else 0 := by
  rw [←triFacesAt_card hsupport v]
  simp only [triFacesAt,Finset.card_filter,triFaceVertices,Finset.mem_image,Finset.mem_univ,true_and]

#print axioms triFacesAt_card
#print axioms triangle_incidence_indicator
#print axioms triFaceVertices_injective
#print axioms triFaceVertex_turn
end Blueprint.Thomson.Tail.Implementation
