import AllS.Units.N_GI.N_cube_k4_noE.N_local_quad

set_option maxHeartbeats 500000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem contactTriangleFlag_incidence_pos {Y : Fin 8 → Point} {c : ℝ}
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (d : ContactDart Y c)
    (hflag : contactTriangleFlag hY hc d=true) :
    0 < faceCornerCount (boundaryArray Y c hY hc 3) d.1 := by
  rw [←contactTriangleFlag_vertex_count]
  apply Finset.sum_pos'
  · intro i _;split_ifs <;> omega
  · exact ⟨d.2,Finset.mem_univ _,by rw [hflag];decide⟩

theorem sharedTriangle_third_avoiding {Y : Fin 8 → Point} {c : ℝ}
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hirr : PackingIrreducible c Y)
    (v w z : Fin 8) (hadj : (sharedTriangleGraph hY hc).Adj v w) :
    ∃a : Fin 8,a≠z ∧ ContactAdj Y c v a ∧ ContactAdj Y c w a ∧
      0 < faceCornerCount (boundaryArray Y c hY hc 3) a := by
  obtain ⟨q,rfl,hf,hr⟩ := hadj
  let d : ContactDart Y c := ⟨v,q⟩
  let F := contactFaceNext Y c hY hc
  have build (d : ContactDart Y c) (hd : contactTriangleFlag hY hc d=true) :
      ContactAdj Y c d.1 (F d).2.val ∧ ContactAdj Y c d.2.val (F d).2.val ∧
        0 < faceCornerCount (boundaryArray Y c hY hc 3) (F d).2.val := by
    refine ⟨⟨(contactFaceNext_no_backtrack Y c hY hc hirr d).symm,
      contactTriangleFlag_closing_contact hY hc hirr d hd⟩,
      ⟨(F d).2.property.1.symm,(F d).2.property.2⟩,?_⟩
    apply contactTriangleFlag_incidence_pos hY hc (F (F d))
    rw [contactTriangleFlag_next,contactTriangleFlag_next]
    exact hd
  by_cases hz : (F d).2.val=z
  · refine ⟨(F (contactReverse Y c d)).2.val,?_,?_,?_,?_⟩
    · intro he
      exact sharedTriangle_thirds_distinct hY hc hirr d hf hr (hz.trans he.symm)
    · exact (build (contactReverse Y c d) hr).2.1
    · exact (build (contactReverse Y c d) hr).1
    · exact (build (contactReverse Y c d) hr).2.2
  · exact ⟨(F d).2.val,hz,(build d hf).1,(build d hf).2.1,(build d hf).2.2⟩

#print axioms sharedTriangle_third_avoiding
end Blueprint.Thomson.Tail.Implementation
