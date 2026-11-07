import AllS.Units.N_GI.N_cube_k4_noE.N_s_components
import AllS.Units.N_GI.N_cube_k4_noE.N_finite_neighbors

set_option maxHeartbeats 1200000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem cube_k4_noE_four_path_false (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (v : Fin 4 → Fin 8) (hinj : Function.Injective v)
    (hfull : ∀z,Fintype.card (ContactNeighbor Y c z)=4 ↔ ∃i,v i=z)
    (hpat : ∀i j,(sharedTriangleGraph hY hc).Adj (v i) (v j) ↔ fourGraphAdj (fourPatternBits 1) i j) : False := by
  let S := sharedTriangleGraph hY hc
  let d := fun z => Fintype.card (ContactNeighbor Y c z)
  let t := faceCornerCount (boundaryArray Y c hY hc 3)
  have hs := auxiliary_graphs_shared_triangle_degrees Y c hY hc hcupper hirr hbound hne hsupport
  have ht := (rhombus_angles_assemble Y c hY hc hcupper hirr hbound hne hsupport).1
  have hv4 (i : Fin 4) : d (v i)=4 := (hfull _).mpr ⟨i,rfl⟩
  have hs01 : S.Adj (v 0) (v 1) := (hpat 0 1).mpr (by decide +kernel)
  have hs12 : S.Adj (v 1) (v 2) := (hpat 1 2).mpr (by decide +kernel)
  have hs23 : S.Adj (v 2) (v 3) := (hpat 2 3).mpr (by decide +kernel)
  have h01 := sharedTriangleGraph_subgraph hY hc hs01
  have h12 := sharedTriangleGraph_subgraph hY hc hs12
  have h23 := sharedTriangleGraph_subgraph hY hc hs23
  have h02 : inner ℝ (Y (v 0)) (Y (v 2))=c := hs.2.2 (v 1) (v 0) (v 2)
    (fun h => (by decide : (0:Fin 4)≠2) (hinj h)) (S.adj_symm hs01) hs12
  have h13 : inner ℝ (Y (v 1)) (Y (v 3))=c := hs.2.2 (v 2) (v 1) (v 3)
    (fun h => (by decide : (1:Fin 4)≠3) (hinj h)) (S.adj_symm hs12) hs23
  obtain ⟨a,ha2,h0a,h1a,hta⟩ := sharedTriangle_third_avoiding hY hc hirr (v 0) (v 1) (v 2) hs01
  have ha0 : a≠v 0 := h0a.1.symm
  have ha1 : a≠v 1 := h1a.1.symm
  have ha3 : a≠v 3 := by
    intro he
    exact no_four_six_inner_products Y c hY.1 hc.1.le hcupper (v 0) (v 1) (v 2) (v 3)
      h01.2 h02 (he ▸ h0a.2) h12.2 h13 h23.2
  have ha4 : d a≠4 := by
    intro hh
    obtain ⟨i,hi⟩ := (hfull a).mp hh
    fin_cases i
    · exact ha0 hi.symm
    · exact ha1 hi.symm
    · exact ha2 hi.symm
    · exact ha3 hi.symm
  have hda : d a=3 := by
    have hh := degree_degree_four Y c hY hc.1 hcupper hirr hbound a
      (covering_no_rattlers Y c hY hc hcupper hirr hbound hne hsupport a)
    rw [←contactNeighbor_card_eq] at hh
    change Fintype.card (ContactNeighbor Y c a)≠4 at ha4
    change Fintype.card (ContactNeighbor Y c a)=3
    omega
  have hta1 : t a=1 := by
    have hh := (ht a).1 hda
    change t a≤1 at hh
    change 0<t a at hta
    omega
  have hnotS1a : ¬S.Adj (v 1) a := fun h => ha4 ((hs.2.1 _ _ h).2)
  obtain ⟨z,hza,h1z,hnotS1z,hDaz⟩ := unshared_contact_opposite hY hc hcupper hirr hsupport (v 1) a h1a hnotS1a
  let f : Fin 4 → Fin 8 := ![v 0,v 2,v 3,a]
  have hf : Function.Injective f := by
    intro i j hh
    fin_cases i <;> fin_cases j
    all_goals try rfl
    all_goals dsimp [f] at hh
    all_goals first
      | exact (ha0 hh).elim | exact (ha0 hh.symm).elim
      | exact (ha2 hh).elim | exact (ha2 hh.symm).elim
      | exact (ha3 hh).elim | exact (ha3 hh.symm).elim
      | have hi := hinj hh;have hv := congrArg Fin.val hi;norm_num at hv
  have hfc (i : Fin 4) : (actualContactGraph Y c).Adj (v 1) (f i) := by
    fin_cases i
    · exact (actualContactGraph Y c).adj_symm h01
    · exact h12
    · exact ⟨fun h => (by decide : (1:Fin 4)≠3) (hinj h),h13⟩
    · exact h1a
  obtain ⟨i,hi⟩ := graph_neighbors_exhaust (actualContactGraph Y c) (v 1) 4 f hf
    ((actualContactGraph_degree Y c (v 1)).trans (hv4 1)) hfc z h1z
  have hz3 : z=v 3 := by
    fin_cases i
    · exact (hnotS1z (hi ▸ S.adj_symm hs01)).elim
    · exact (hnotS1z (hi ▸ hs12)).elim
    · exact hi.symm
    · exact (hza hi.symm).elim
  have hS3 : S.degree (v 3)≤1 := by
    rw [←S.card_neighborFinset_eq_degree]
    apply Finset.card_le_one.mpr
    intro x hx y hy
    have hneigh (w : Fin 8) (hw : w∈S.neighborFinset (v 3)) : w=v 2 := by
      have hadj := (S.mem_neighborFinset _ _).mp hw
      obtain ⟨j,rfl⟩ := (hfull w).mp (hs.2.1 _ _ hadj).2
      have hp := (hpat 3 j).mp hadj
      have hidx : ∀j : Fin 4,fourGraphAdj (fourPatternBits 1) 3 j → j=2 := by decide +kernel
      exact congrArg v (hidx j hp)
    exact (hneigh x hx).trans (hneigh y hy).symm
  have ht3 : t (v 3)≤2 := by
    have hh := (ht (v 3)).2 (hv4 3)
    change t (v 3)≤3 at hh
    have hnot : t (v 3)≠3 := by
      intro he
      have hd2 := (hs.1 (v 3)).2.1.mpr ⟨hv4 3,he⟩
      change S.degree (v 3)=2 at hd2
      omega
    omega
  have hD : (diagonalGraph hsupport).Adj (v 3) a := (diagonalGraph hsupport).adj_symm (hz3 ▸ hDaz)
  exact (diagonalGraph_no_mixed_types Y c hY hc hcupper hirr hbound hne hsupport (v 3) a hD).2.2
    ⟨hv4 3,ht3,hda,hta1⟩

#print axioms cube_k4_noE_four_path_false
end Blueprint.Thomson.Tail.Implementation
