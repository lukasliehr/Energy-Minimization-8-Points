import AllS.Units.N_GI.N_cube_k4.N_types_fixed

set_option maxHeartbeats 3000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem degree_three_four_count (d : Fin 8 → ℕ) (hd : ∀ v,d v=3 ∨ d v=4) :
    (Finset.univ.filter (fun v => d v=3)).card+(Finset.univ.filter (fun v => d v=4)).card=8 := by
  have hv (v : Fin 8) : (if d v=3 then 1 else 0)+(if d v=4 then 1 else 0)=(1:ℕ) := by
    rcases hd v with h | h <;> simp [h]
  have hh := congrArg (fun f : Fin 8 → ℕ => ∑ v,f v) (funext hv)
  simpa only [Finset.card_filter,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,mul_one] using hh

theorem quad_not_in_four_vertex_diagonal_class (D G : SimpleGraph (Fin 8))
    (C : Finset (Fin 8)) (hC : C.card=4) (v : Fin 4 → Fin 8)
    (hinj : Function.Injective v) (hside : ∀ i,G.Adj (v i) (v (i+1)))
    (hdisjoint : ∀ a b,D.Adj a b → ¬G.Adj a b)
    (hclosed : ∀ a∈C,∀ b,D.Adj a b → b∈C)
    (hdegree : D.degree (v 0)=2) : ¬∀ i,v i∈C := by
  intro hall
  have himage : Finset.univ.image v=C := by
    apply Finset.eq_of_subset_of_card_le
    · intro a ha
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
      exact hall i
    · rw [Finset.card_image_of_injective _ hinj,Finset.card_univ,Fintype.card_fin,hC]
  have hsub : D.neighborFinset (v 0)⊆{v 2} := by
    intro a ha
    have hadj := (D.mem_neighborFinset _ _).mp ha
    have hac := hclosed (v 0) (hall 0) a hadj
    rw [←himage] at hac
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hac
    fin_cases i
    · exact (D.irrefl hadj).elim
    · exact (hdisjoint _ _ hadj (hside 0)).elim
    · exact Finset.mem_singleton.mpr rfl
    · exact (hdisjoint _ _ hadj (G.adj_symm (hside 3))).elim
  have hh := Finset.card_le_card hsub
  rw [SimpleGraph.card_neighborFinset_eq_degree,hdegree,Finset.card_singleton] at hh
  omega

theorem cube_k4_quads_alternate (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=4)
    (hnoE : ∀ v,Fintype.card (ContactNeighbor Y c v)=4 →
      faceCornerCount (boundaryArray Y c hY hc 3) v≠3)
    (f : QuadFace Y c hY hc) :
    let d := fun v => Fintype.card (ContactNeighbor Y c v)
    ∀ i, d (quadFaceVertex f i)≠d (quadFaceVertex f (i+1)) ∧
      d (quadFaceVertex f i)=d (quadFaceVertex f (i+2)) := by
  let d := fun v => Fintype.card (ContactNeighbor Y c v)
  let t := faceCornerCount (boundaryArray Y c hY hc 3)
  let D := diagonalGraph hsupport
  have ha := covering_no_rattlers Y c hY hc hcupper hirr hbound hne hsupport
  have hd (v : Fin 8) : d v=3 ∨ d v=4 := by
    have hh := degree_degree_four Y c hY hc.1 hcupper hirr hbound v (ha v)
    rw [←contactNeighbor_card_eq] at hh
    change Fintype.card (ContactNeighbor Y c v)=3 ∨ Fintype.card (ContactNeighbor Y c v)=4
    omega
  have ht := cube_k4_types_fixed Y c hY hc hcupper hirr hbound hne hsupport hk hnoE
  have hpres (v w : Fin 8) (hadj : D.Adj v w) : d v=d w := by
    have hnot := (diagonalGraph_no_mixed_types Y c hY hc hcupper hirr hbound hne hsupport v w hadj).2.2
    have hrev := (diagonalGraph_no_mixed_types Y c hY hc hcupper hirr hbound hne hsupport w v
      (D.adj_symm hadj)).2.2
    rcases hd v with hv | hv <;> rcases hd w with hw | hw
    · exact hv.trans hw.symm
    · exact (hrev ⟨hw,((ht w).2 hw).le,hv,(ht v).1 hv⟩).elim
    · exact (hnot ⟨hv,((ht v).2 hv).le,hw,(ht w).1 hw⟩).elim
    · exact hv.trans hw.symm
  have hdeg (v : Fin 8) : D.degree v=2 := by
    have hh := auxiliary_graphs_diagonal_degrees Y c hY hc hcupper hirr hsupport v
    change D.degree v+faceCornerCount (boundaryArray Y c hY hc 3) v=
      Fintype.card (ContactNeighbor Y c v) at hh
    rcases hd v with hv | hv
    · have htt := (ht v).1 hv
      change Fintype.card (ContactNeighbor Y c v)=3 at hv
      rw [htt,hv] at hh
      omega
    · have htt := (ht v).2 hv
      change Fintype.card (ContactNeighbor Y c v)=4 at hv
      rw [htt,hv] at hh
      omega
  let v := quadFaceVertex f
  have hopp (i : Fin 4) : d (v i)=d (v (i+2)) := hpres _ _ ⟨f,i,rfl,rfl⟩
  have hclass : (Finset.univ.filter (fun a => d a=d (v 0))).card=4 := by
    have hc34 := degree_three_four_count d hd
    have hc3 : (Finset.univ.filter (fun a => d a=3)).card=4 := hk
    rcases hd (v 0) with hh | hh
    · rw [hh]
      exact hc3
    · rw [hh]
      omega
  have hnot : ¬∀ i,d (v i)=d (v 0) := by
    intro hall
    apply quad_not_in_four_vertex_diagonal_class D (actualContactGraph Y c)
      (Finset.univ.filter (fun a => d a=d (v 0))) hclass v
      (quadFaceVertex_injective f hsupport)
      (fun i => ⟨fun he => (show i≠i+1 by fin_cases i <;> decide)
        (quadFaceVertex_injective f hsupport he),quadFaceVertex_side f i⟩)
      (fun a b hab hcontact => (diagonalGraph_noncontact hirr hbound hsupport a b hab).ne hcontact.2)
      (fun a ha b hab => Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (hpres a b hab).symm.trans (Finset.mem_filter.mp ha).2⟩) (hdeg (v 0))
    intro i
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hall i⟩
  have h01 : d (v 0)≠d (v 1) := by
    intro he
    apply hnot
    intro i
    fin_cases i
    · rfl
    · exact he.symm
    · exact (hopp 0).symm
    · exact (hopp 1).symm.trans he.symm
  have h02 := hopp 0
  have h13 := hopp 1
  change d (v 0)=d (v 2) at h02
  change d (v 1)=d (v 3) at h13
  change ∀ i,d (v i)≠d (v (i+1)) ∧ d (v i)=d (v (i+2))
  intro i
  refine ⟨?_,hopp i⟩
  fin_cases i
  · exact h01
  · exact fun h => h01 (h02.trans h.symm)
  · exact fun h => h01 (h02.trans (h.trans h13.symm))
  · exact fun h => h01 (h13.trans h).symm

#print axioms cube_k4_quads_alternate
#print axioms quad_not_in_four_vertex_diagonal_class
end Blueprint.Thomson.Tail.Implementation
