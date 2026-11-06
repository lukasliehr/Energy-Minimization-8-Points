import AllS.Units.N_GI.N_matching_delete.N_quad_assembly

set_option maxHeartbeats 500000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem triFaceDart_flag_true {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : TriFace Y c hY hc) (i : Fin 3) :
    contactTriangleFlag hY hc (triFaceDart f i)=true := by
  have hh := contactTriangleFlag_orbit_point hY hc f.val (Fin.cast f.property.symm i)
  have hn : decide ((boundaryOrbitCycle Y c hY hc f.val).size+1=3)=true := by
    rw [f.property]
    rfl
  exact hh.trans hn

theorem triFace_oriented_index {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f : TriFace Y c hY hc) (v w : Fin 8) (hvw : v≠w)
    (hv : v∈triFaceVertices f) (hw : w∈triFaceVertices f) :
    (∃i : Fin 3,triFaceVertex f i=v ∧ triFaceVertex f (i+1)=w) ∨
    (∃i : Fin 3,triFaceVertex f i=w ∧ triFaceVertex f (i+1)=v) := by
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hv
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hw
  have hij : i≠j := fun h => hvw (hi.symm.trans ((congrArg (triFaceVertex f) h).trans hj))
  have hcases : ∀i j : Fin 3,i≠j → j=i+1 ∨ i=j+1 := by decide
  rcases hcases i j hij with h | h
  · exact Or.inl ⟨i,hi,h ▸ hj⟩
  · exact Or.inr ⟨j,hj,h ▸ hi⟩

theorem triFaces_common_edge_shared {Y : Fin 8 → Point} {c : ℝ} {hY : IsConfiguration Y}
    {hc : c ∈ Set.Ioo (0:ℝ) 1} (f g : TriFace Y c hY hc) (hfg : f≠g)
    (v w : Fin 8) (hadj : ContactAdj Y c v w)
    (hvf : v∈triFaceVertices f) (hwf : w∈triFaceVertices f)
    (hvg : v∈triFaceVertices g) (hwg : w∈triFaceVertices g) :
    (sharedTriangleGraph hY hc).Adj v w := by
  have build (f g : TriFace Y c hY hc) (i j : Fin 3)
      (hfi : triFaceVertex f i=v) (hfn : triFaceVertex f (i+1)=w)
      (hgj : triFaceVertex g j=w) (hgn : triFaceVertex g (j+1)=v) :
      (sharedTriangleGraph hY hc).Adj v w := by
    let q : ContactNeighbor Y c v := ⟨w,hadj.1.symm,hadj.2⟩
    have hf : triFaceDart f i=⟨v,q⟩ := contactDart_ext hfi ((triFaceDart_tip f i).trans hfn)
    have hg : triFaceDart g j=contactReverse Y c ⟨v,q⟩ := contactDart_ext hgj ((triFaceDart_tip g j).trans hgn)
    refine ⟨q,rfl,?_,?_⟩
    · exact (congrArg (contactTriangleFlag hY hc) hf).symm.trans (triFaceDart_flag_true f i)
    · exact (congrArg (contactTriangleFlag hY hc) hg).symm.trans (triFaceDart_flag_true g j)
  rcases triFace_oriented_index f v w hadj.1 hvf hwf with ⟨i,hi,hi'⟩ | ⟨i,hi,hi'⟩
  · rcases triFace_oriented_index g v w hadj.1 hvg hwg with ⟨j,hj,hj'⟩ | ⟨j,hj,hj'⟩
    · exact (hfg (triFace_oriented_edge_unique f g i j (hi.trans hj.symm) (hi'.trans hj'.symm))).elim
    · exact build f g i j hi hi' hj hj'
  · rcases triFace_oriented_index g v w hadj.1 hvg hwg with ⟨j,hj,hj'⟩ | ⟨j,hj,hj'⟩
    · exact build g f j i hj hj' hi hi'
    · exact (hfg (triFace_oriented_edge_unique f g i j (hi.trans hj.symm) (hi'.trans hj'.symm))).elim

theorem sharedTriangleGraph_subgraph {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) : sharedTriangleGraph hY hc≤actualContactGraph Y c := by
  rintro v w ⟨q,rfl,_,_⟩
  exact ⟨q.property.1.symm,q.property.2⟩

theorem sharedTriangleGraph_flag {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (d : ContactDart Y c)
    (hadj : (sharedTriangleGraph hY hc).Adj d.1 d.2.val) : contactTriangleFlag hY hc d=true := by
  obtain ⟨q,hq,hf,hr⟩ := hadj
  have he : (⟨d.1,q⟩ : ContactDart Y c)=d := contactDart_ext rfl hq
  exact (congrArg (contactTriangleFlag hY hc) he).symm.trans hf

theorem triangle_deletion_from_face_sides {Y : Fin 8 → Point} {c : ℝ} (hY : IsConfiguration Y)
    (hc : c ∈ Set.Ioo (0:ℝ) 1) (M : SimpleGraph (Fin 8))
    (hside : ∀f : TriFace Y c hY hc,∃i : Fin 3,M.Adj (triFaceVertex f i) (triFaceVertex f (i+1)))
    (d : ContactDart Y c) (hflag : contactTriangleFlag hY hc d=true) :
    let F := contactFaceNext Y c hY hc
    M.Adj d.1 d.2.val ∨ M.Adj (F d).1 (F d).2.val ∨ M.Adj (F (F d)).1 (F (F d)).2.val := by
  obtain ⟨f,i,rfl⟩ := triangle_contactDart_face hY hc d hflag
  obtain ⟨j,hj⟩ := hside f
  have hjd : M.Adj (triFaceDart f j).1 (triFaceDart f j).2.val := by
    rw [triFaceDart_tip]
    exact hj
  have hcases : ∀i j : Fin 3,j=i ∨ j=i+1 ∨ j=i+2 := by decide
  dsimp only
  rcases hcases i j with h | h | h
  · exact Or.inl (h ▸ hjd)
  · refine Or.inr (Or.inl ?_)
    rw [triFaceDart_next]
    exact h ▸ hjd
  · refine Or.inr (Or.inr ?_)
    rw [triFaceDart_next,triFaceDart_next,show i+1+1=i+2 by fin_cases i <;> decide]
    exact h ▸ hjd

#print axioms triFaces_common_edge_shared
#print axioms triangle_deletion_from_face_sides
end Blueprint.Thomson.Tail.Implementation
