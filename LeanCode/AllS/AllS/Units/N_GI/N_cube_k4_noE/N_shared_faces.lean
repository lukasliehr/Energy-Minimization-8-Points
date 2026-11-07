import AllS.Units.N_GI.N_cube_k4_noE.N_finite_neighbors

set_option maxHeartbeats 800000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem triFaceVertices_rotate {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : TriFace Y c hY hc) (i : Fin 3) :
    triFaceVertices f={triFaceVertex f i,triFaceVertex f (i+1),triFaceVertex f (i+2)} := by
  apply Finset.ext
  intro z
  simp only [triFaceVertices,Finset.mem_image,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro ⟨j,rfl⟩
    have h : ∀i j : Fin 3,j=i ∨ j=i+1 ∨ j=i+2 := by decide
    rcases h i j with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨i,rfl⟩
    · exact ⟨i+1,rfl⟩
    · exact ⟨i+2,rfl⟩

theorem triangleFlag_face_vertices {Y : Fin 8 → Point} {c : ℝ}
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (d : ContactDart Y c)
    (hd : contactTriangleFlag hY hc d=true) :
    ∃ f : TriFace Y c hY hc,triFaceVertices f={d.1,d.2.val,(contactFaceNext Y c hY hc d).2.val} := by
  obtain ⟨f,i,rfl⟩ := triangle_contactDart_face hY hc d hd
  refine ⟨f,?_⟩
  rw [triFaceDart_next,triFaceDart_tip,triFaceDart_tip]
  change triFaceVertices f={triFaceVertex f i,triFaceVertex f (i+1),triFaceVertex f (i+1+1)}
  rw [show i+1+1=i+2 by fin_cases i <;> decide]
  exact triFaceVertices_rotate f i

theorem sharedTriangle_face_avoiding {Y : Fin 8 → Point} {c : ℝ}
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hirr : PackingIrreducible c Y)
    (v w z : Fin 8) (hadj : (sharedTriangleGraph hY hc).Adj v w) :
    ∃a : Fin 8,∃f : TriFace Y c hY hc,a≠z ∧ ContactAdj Y c v a ∧ ContactAdj Y c w a ∧
      triFaceVertices f={v,w,a} := by
  obtain ⟨q,rfl,hf,hr⟩ := hadj
  let d : ContactDart Y c := ⟨v,q⟩
  let F := contactFaceNext Y c hY hc
  have build (d : ContactDart Y c) (hd : contactTriangleFlag hY hc d=true) :
      ContactAdj Y c d.1 (F d).2.val ∧ ContactAdj Y c d.2.val (F d).2.val :=
    ⟨⟨(contactFaceNext_no_backtrack Y c hY hc hirr d).symm,
      contactTriangleFlag_closing_contact hY hc hirr d hd⟩,
      ⟨(F d).2.property.1.symm,(F d).2.property.2⟩⟩
  by_cases hz : (F d).2.val=z
  · obtain ⟨f,hfset⟩ := triangleFlag_face_vertices hY hc (contactReverse Y c d) hr
    refine ⟨(F (contactReverse Y c d)).2.val,f,?_,(build _ hr).2,(build _ hr).1,?_⟩
    · intro he
      exact sharedTriangle_thirds_distinct hY hc hirr d hf hr (hz.trans he.symm)
    · exact hfset.trans (Finset.insert_comm _ _ _)
  · obtain ⟨f,hfset⟩ := triangleFlag_face_vertices hY hc d hf
    exact ⟨(F d).2.val,f,hz,(build d hf).1,(build d hf).2,hfset⟩

theorem sharedTriangle_face_common {Y : Fin 8 → Point} {c : ℝ}
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hirr : PackingIrreducible c Y)
    (v w z : Fin 8) (hadj : (sharedTriangleGraph hY hc).Adj v w)
    (hvz : ContactAdj Y c v z) (hwz : ContactAdj Y c w z) :
    ∃f : TriFace Y c hY hc,triFaceVertices f={v,w,z} := by
  obtain ⟨q,rfl,hf,hr⟩ := hadj
  let d : ContactDart Y c := ⟨v,q⟩
  let F := contactFaceNext Y c hY hc
  let a := (F d).2.val
  let b := (F (contactReverse Y c d)).2.val
  have hne : Y a≠Y b := fun hh => sharedTriangle_thirds_distinct hY hc hirr d hf hr (hY.2 hh)
  have hcases : z=a ∨ z=b := by
    have hvw : Y v≠Y q.val := fun hh => q.property.1 (hY.2 hh).symm
    have hh := common_contact_neighbors_exhaust (Y v) (Y a) (Y q.val) (Y b) (Y z) c
      (hY.1 _) (hY.1 _) (hY.1 _) (hY.1 _) (hY.1 _) hc.1 hvw hne
      (contactTriangleFlag_closing_contact hY hc hirr d hf) (F d).2.property.2
      (F (contactReverse Y c d)).2.property.2
      (contactTriangleFlag_closing_contact hY hc hirr (contactReverse Y c d) hr) hvz.2 hwz.2
    exact hh.imp (fun h => hY.2 h) (fun h => hY.2 h)
  rcases hcases with rfl | rfl
  · exact triangleFlag_face_vertices hY hc d hf
  · obtain ⟨f,hfset⟩ := triangleFlag_face_vertices hY hc (contactReverse Y c d) hr
    exact ⟨f,hfset.trans (Finset.insert_comm _ _ _)⟩

theorem triFace_mem_incidence_pos {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (f : TriFace Y c hY hc) (z : Fin 8) (hz : z∈triFaceVertices f) :
    0<faceCornerCount (boundaryArray Y c hY hc 3) z := by
  rw [triangle_incidence_indicator hsupport]
  apply Finset.sum_pos'
  · intro i _;split_ifs <;> omega
  · exact ⟨f,Finset.mem_univ _,by rw [if_pos hz];decide⟩

#print axioms sharedTriangle_face_avoiding
#print axioms sharedTriangle_face_common
end Blueprint.Thomson.Tail.Implementation
