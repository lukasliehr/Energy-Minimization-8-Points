import AllS.Units.N_GI.N_matching_delete.N_unchanged_faces

set_option maxHeartbeats 600000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

def cubicQuadOfFourCycles (R : CubicRotationData)
    (hfaces : ∀d : R.graph.Dart,∃A : Fin 4 → R.graph.Dart,∃i : Fin 4,
      A i=d ∧ (∀j,R.faceNext (A j)=A (j+1)) ∧
      ∀j,(A j).fst≠(A (j+1)).snd ∧ ¬R.graph.Adj (A j).fst (A (j+1)).snd) : CubicQuadData where
  toCubicRotationData := R
  face_four d := by
    obtain ⟨A,i,hi,hs,ho⟩ := hfaces d
    rw [←hi,hs,hs,hs,hs]
    congr 1
    fin_cases i <;> decide
  opposite_distinct d := by
    obtain ⟨A,i,hi,hs,ho⟩ := hfaces d
    rw [←hi,hs]
    exact (ho i).1
  opposite_nonadjacent d := by
    obtain ⟨A,i,hi,hs,ho⟩ := hfaces d
    rw [←hi,hs]
    exact (ho i).2

theorem deletedActualFourFaces {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10) (hirr : PackingIrreducible c Y)
    (hbound : PackingInnerBound c Y)
    (hsupport : ∀C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (M : SimpleGraph (Fin 8)) (hM : M≤actualContactGraph Y c)
    (hd : ∀v,Fintype.card (ContactNeighbor Y c v)=3 ∨ Fintype.card (ContactNeighbor Y c v)=4)
    (hMdegree : ∀v,M.degree v+3=Fintype.card (ContactNeighbor Y c v))
    (hMtri : ∀d : ContactDart Y c,M.Adj d.1 d.2.val → contactTriangleFlag hY hc d=true)
    (hdelete : ∀d : ContactDart Y c,contactTriangleFlag hY hc d=true →
      let F := contactFaceNext Y c hY hc
      M.Adj d.1 d.2.val ∨ M.Adj (F d).1 (F d).2.val ∨ M.Adj (F (F d)).1 (F (F d)).2.val) :
    let R := deletedActualRotation hY hc M hM hd hMdegree
    ∀d : R.graph.Dart,∃A : Fin 4 → R.graph.Dart,∃i : Fin 4,
      A i=d ∧ (∀j,R.faceNext (A j)=A (j+1)) ∧
      ∀j,(A j).fst≠(A (j+1)).snd ∧ ¬R.graph.Adj (A j).fst (A (j+1)).snd := by
  let F := contactFaceNext Y c hY hc
  let t := contactReverse Y c
  let R := deletedActualRotation hY hc M hM hd hMdegree
  have hdeg (v : Fin 8) : M.degree v≤1 := by
    have hm := hMdegree v
    rcases hd v with h | h <;> omega
  dsimp only
  intro d
  let r := retainedDartToContact M d
  have merged (s : ContactDart Y c) (hs : M.Adj s.1 s.2.val) (i : Fin 4)
      (heq : mergedTriangleDart hY hc s i=r) :
      ∃A : Fin 4 → R.graph.Dart,∃i : Fin 4,
        A i=d ∧ (∀j,R.faceNext (A j)=A (j+1)) ∧
        ∀j,(A j).fst≠(A (j+1)).snd ∧ ¬R.graph.Adj (A j).fst (A (j+1)).snd := by
    have hf := hMtri s hs
    have ht := hMtri (t s) (M.adj_symm hs)
    let A := mergedRetainedDart hY hc hirr M hdeg s hs hf ht
    refine ⟨A,i,?_,?_,?_⟩
    · apply retainedDartToContact_injective M
      exact heq
    · intro j
      exact mergedRetainedDart_step hY hc hirr M hM hd hMdegree hdeg s hs hf ht j
    · intro j
      exact mergedTriangleDart_opposite hY hc hcupper hirr M s hs hf ht j
  by_cases hflag : contactTriangleFlag hY hc r=true
  · have h3 : F (F (F r))=r := contactTriangleFlag_three hY hc r hflag
    rcases hdelete r hflag with h | h | h
    · exact (d.adj.2 h).elim
    · apply merged (F r) h 1
      exact h3
    · apply merged (F (F r)) h 0
      exact h3
  · obtain ⟨f,i,hi⟩ := nontriangle_contactDart_quad hY hc hcupper hirr hsupport r hflag
    refine ⟨quadRetainedDart M hMtri f,i,?_,?_,?_⟩
    · apply retainedDartToContact_injective M
      exact hi
    · intro j
      exact quadRetainedDart_step hY hc M hM hd hMdegree hMtri f j
    · intro j
      exact quadRetainedDart_opposite hY hc hirr hbound hsupport M hMtri f j

def matchingDeletedQuad {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10) (hirr : PackingIrreducible c Y)
    (hbound : PackingInnerBound c Y)
    (hsupport : ∀C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (M : SimpleGraph (Fin 8)) (hM : M≤actualContactGraph Y c)
    (hd : ∀v,Fintype.card (ContactNeighbor Y c v)=3 ∨ Fintype.card (ContactNeighbor Y c v)=4)
    (hMdegree : ∀v,M.degree v+3=Fintype.card (ContactNeighbor Y c v))
    (hMtri : ∀d : ContactDart Y c,M.Adj d.1 d.2.val → contactTriangleFlag hY hc d=true)
    (hdelete : ∀d : ContactDart Y c,contactTriangleFlag hY hc d=true →
      let F := contactFaceNext Y c hY hc
      M.Adj d.1 d.2.val ∨ M.Adj (F d).1 (F d).2.val ∨ M.Adj (F (F d)).1 (F (F d)).2.val) :
    CubicQuadData :=
  cubicQuadOfFourCycles (deletedActualRotation hY hc M hM hd hMdegree)
    (deletedActualFourFaces hY hc hcupper hirr hbound hsupport M hM hd hMdegree hMtri hdelete)

theorem matching_delete_spanning_cube {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10) (hirr : PackingIrreducible c Y)
    (hbound : PackingInnerBound c Y)
    (hsupport : ∀C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (M : SimpleGraph (Fin 8)) (hM : M≤actualContactGraph Y c)
    (hd : ∀v,Fintype.card (ContactNeighbor Y c v)=3 ∨ Fintype.card (ContactNeighbor Y c v)=4)
    (hMdegree : ∀v,M.degree v+3=Fintype.card (ContactNeighbor Y c v))
    (hMtri : ∀d : ContactDart Y c,M.Adj d.1 d.2.val → contactTriangleFlag hY hc d=true)
    (hdelete : ∀d : ContactDart Y c,contactTriangleFlag hY hc d=true →
      let F := contactFaceNext Y c hY hc
      M.Adj d.1 d.2.val ∨ M.Adj (F d).1 (F d).2.val ∨ M.Adj (F (F d)).1 (F (F d)).2.val) :
    HasSpanningCube (actualContactGraph Y c) := by
  let Q := matchingDeletedQuad hY hc hcupper hirr hbound hsupport M hM hd hMdegree hMtri hdelete
  obtain ⟨e,he⟩ := cubic_quads_cube_labeling Q
  exact ⟨e,fun i j hij => (he i j hij).1⟩

#print axioms deletedActualFourFaces
#print axioms matching_delete_spanning_cube
end Blueprint.Thomson.Tail.Implementation
