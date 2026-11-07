import AllS.Units.N_GI.N_cube_k4_noE.N_pattern_counts

set_option maxHeartbeats 1500000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem cube_k4_noE_triangle_false (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc,C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=4)
    (v : Fin 4 → Fin 8) (hinj : Function.Injective v)
    (hfull : ∀z,Fintype.card (ContactNeighbor Y c z)=4 ↔ ∃i,v i=z)
    (hpat : ∀i j,(sharedTriangleGraph hY hc).Adj (v i) (v j) ↔ fourGraphAdj (fourPatternBits 2) i j) : False := by
  let S := sharedTriangleGraph hY hc
  let d := fun z => Fintype.card (ContactNeighbor Y c z)
  let t := faceCornerCount (boundaryArray Y c hY hc 3)
  let D := diagonalGraph hsupport
  have hs := auxiliary_graphs_shared_triangle_degrees Y c hY hc hcupper hirr hbound hne hsupport
  have ht := (rhombus_angles_assemble Y c hY hc hcupper hirr hbound hne hsupport).1
  have hv4 (i : Fin 4) : d (v i)=4 := (hfull _).mpr ⟨i,rfl⟩
  have hvne (i j : Fin 4) (h : i≠j) : v i≠v j := fun hh => h (hinj hh)
  have hn01 := hvne 0 1 (by decide)
  have hn02 := hvne 0 2 (by decide)
  have hn12 := hvne 1 2 (by decide)
  have hn30 := hvne 3 0 (by decide)
  have hn31 := hvne 3 1 (by decide)
  have hn32 := hvne 3 2 (by decide)
  have hs01 : S.Adj (v 0) (v 1) := (hpat 0 1).mpr (by decide +kernel)
  have hs12 : S.Adj (v 1) (v 2) := (hpat 1 2).mpr (by decide +kernel)
  have hs02 : S.Adj (v 0) (v 2) := (hpat 0 2).mpr (by decide +kernel)
  have h01 := sharedTriangleGraph_subgraph hY hc hs01
  have h12 := sharedTriangleGraph_subgraph hY hc hs12
  have h02 := sharedTriangleGraph_subgraph hY hc hs02
  obtain ⟨f0,hf0⟩ := sharedTriangle_face_common hY hc hirr (v 0) (v 1) (v 2) hs01 h02 h12
  obtain ⟨a,fa,ha2,h0a,h1a,hfa⟩ := sharedTriangle_face_avoiding hY hc hirr (v 0) (v 1) (v 2) hs01
  obtain ⟨b,fb,hb0,h1b,h2b,hfb⟩ := sharedTriangle_face_avoiding hY hc hirr (v 1) (v 2) (v 0) hs12
  obtain ⟨e,fe,he1,h0e,h2e,hfe⟩ := sharedTriangle_face_avoiding hY hc hirr (v 0) (v 2) (v 1) hs02
  have ha0 := h0a.1.symm
  have ha1 := h1a.1.symm
  have hb1 := h1b.1.symm
  have hb2 := h2b.1.symm
  have he0 := h0e.1.symm
  have he2 := h2e.1.symm
  have hab : a≠b := by
    intro heq
    exact no_four_six_inner_products Y c hY.1 hc.1.le hcupper (v 0) (v 1) (v 2) a
      h01.2 h02.2 h0a.2 h12.2 h1a.2 (heq.symm ▸ h2b.2)
  have hae : a≠e := by
    intro heq
    exact no_four_six_inner_products Y c hY.1 hc.1.le hcupper (v 0) (v 1) (v 2) a
      h01.2 h02.2 h0a.2 h12.2 h1a.2 (heq.symm ▸ h2e.2)
  have hbe : b≠e := by
    intro heq
    exact no_four_six_inner_products Y c hY.1 hc.1.le hcupper (v 0) (v 1) (v 2) b
      h01.2 h02.2 (heq.symm ▸ h0e.2) h12.2 h1b.2 h2b.2
  have hf0a : f0≠fa := triFace_ne_of_member f0 fa (v 2)
    (by simp [hf0]) (by simp [hfa,hn02.symm,hn12.symm,ha2.symm])
  have hf0b : f0≠fb := triFace_ne_of_member f0 fb (v 0)
    (by simp [hf0]) (by simp [hfb,hn01,hn02,hb0.symm])
  have hf0e : f0≠fe := triFace_ne_of_member f0 fe (v 1)
    (by simp [hf0]) (by simp [hfe,hn01.symm,hn12,he1.symm])
  have hfab : fa≠fb := triFace_ne_of_member fa fb (v 0)
    (by simp [hfa]) (by simp [hfb,hn01,hn02,hb0.symm])
  have hfae : fa≠fe := triFace_ne_of_member fa fe (v 1)
    (by simp [hfa]) (by simp [hfe,hn01.symm,hn12,he1.symm])
  have hfbe : fb≠fe := triFace_ne_of_member fb fe (v 1)
    (by simp [hfb]) (by simp [hfe,hn01.symm,hn12,he1.symm])
  have hT : Fintype.card (TriFace Y c hY hc)=4 := by
    have hh := (sphere_euler_assemble Y c hY hc hcupper hirr hbound hne hsupport).2.2.1
    rw [hk] at hh
    exact hh
  have htw : t (v 3)≤1 := by
    have hnroot : v 3∉triFaceVertices f0 := by simp [hf0,hn30,hn31,hn32]
    by_cases hwa : v 3=a
    · apply triangle_incidence_avoid_three hsupport hT f0 fb fe hf0b hf0e hfbe (v 3) hnroot
      · simp [hfb,hwa,ha1,ha2,hab]
      · simp [hfe,hwa,ha0,ha2,hae]
    · by_cases hwb : v 3=b
      · apply triangle_incidence_avoid_three hsupport hT f0 fa fe hf0a hf0e hfae (v 3) hnroot
        · simp [hfa,hwb,hb0,hb1,hab.symm]
        · simp [hfe,hwb,hb0,hb2,hbe]
      · apply triangle_incidence_avoid_three hsupport hT f0 fa fb hf0a hf0b hfab (v 3) hnroot
        · simp [hfa,hn30,hn31,hwa]
        · simp [hfb,hn31,hn32,hwb]
  have hSdeg (i : Fin 4) := shared_pattern_degree S d 2 v hinj hfull hs.2.1 hpat i
  have ht0 : t (v 0)=3 := ((hs.1 (v 0)).2.1.mp ((hSdeg 0).trans (fourPattern_degrees 2 0))).2
  have ht1 : t (v 1)=3 := ((hs.1 (v 1)).2.1.mp ((hSdeg 1).trans (fourPattern_degrees 2 1))).2
  have ht2 : t (v 2)=3 := ((hs.1 (v 2)).2.1.mp ((hSdeg 2).trans (fourPattern_degrees 2 2))).2
  have hH : (Finset.univ.filter (fun z => d z=3 ∧ t z=1)).card=3-t (v 3) := by
    have hh := auxiliary_graphs_incidence_identity Y c hY hc hcupper hirr hbound hne hsupport
    change (∑z,if d z=4 then 3-t z else 0)=_ at hh
    rw [four_labels_deficiency d t v hinj hfull] at hh
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hh
    change (3-t (v 0))+((3-t (v 1))+((3-t (v 2))+(3-t (v 3))))=(Finset.univ.filter (fun z => d z=3 ∧ t z=1)).card at hh
    rw [ht0,ht1,ht2] at hh
    omega
  have hth (z : Fin 8) (hz : d z=3) : t z≤1 := (ht z).1 hz
  have hU : (Finset.univ.filter (fun z => d z=3 ∧ t z=0)).card≤2 := by
    have hh := high_unused_count d t hth hk
    omega
  have hsub : D.neighborFinset (v 3)⊆Finset.univ.filter (fun z => d z=3 ∧ t z=0) := by
    intro z hz
    have hadj := (D.mem_neighborFinset _ _).mp hz
    have hdz : d z=3 ∨ d z=4 := by
      have hh := degree_degree_four Y c hY hc.1 hcupper hirr hbound z
        (covering_no_rattlers Y c hY hc hcupper hirr hbound hne hsupport z)
      rw [←contactNeighbor_card_eq] at hh
      change Fintype.card (ContactNeighbor Y c z)=3 ∨ Fintype.card (ContactNeighbor Y c z)=4
      omega
    rcases hdz with h3 | h4
    · have hb := hth z h3
      have hnot : t z≠1 := fun heq =>
        (diagonalGraph_no_mixed_types Y c hY hc hcupper hirr hbound hne hsupport (v 3) z hadj).2.2
          ⟨hv4 3,by change t (v 3)≤2;omega,h3,heq⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h3,by omega⟩
    · obtain ⟨i,rfl⟩ := (hfull z).mp h4
      have hforbid (j : Fin 4) (hj : t (v j)=3) : ¬D.Adj (v 3) (v j) := fun heq =>
        (diagonalGraph_no_mixed_types Y c hY hc hcupper hirr hbound hne hsupport (v j) (v 3) (D.adj_symm heq)).1
          ⟨hv4 j,hj,hv4 3,by change t (v 3)≤2;omega⟩
      fin_cases i
      · exact (hforbid 0 ht0 hadj).elim
      · exact (hforbid 1 ht1 hadj).elim
      · exact (hforbid 2 ht2 hadj).elim
      · exact (D.irrefl hadj).elim
  have hdegree : D.degree (v 3)≤2 := by
    have hh := Finset.card_le_card hsub
    rw [D.card_neighborFinset_eq_degree] at hh
    omega
  have hh := auxiliary_graphs_diagonal_degrees Y c hY hc hcupper hirr hsupport (v 3)
  change D.degree (v 3)+t (v 3)=d (v 3) at hh
  have hv := hv4 3
  omega

#print axioms cube_k4_noE_triangle_false
end Blueprint.Thomson.Tail.Implementation
