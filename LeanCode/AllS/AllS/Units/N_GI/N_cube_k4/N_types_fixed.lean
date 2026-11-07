import AllS.Units.N_GI.N_cube_k08.N_all_cubic

set_option maxHeartbeats 3000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem four_four_triangle_types (d t : Fin 8 → ℕ)
    (hd : ∀ v,d v=3 ∨ d v=4)
    (hk : (Finset.univ.filter (fun v => d v=3)).card=4)
    (ht3 : ∀ v,d v=3 → t v≤1) (ht4 : ∀ v,d v=4 → t v≤2)
    (hbalance : (∑ v, if d v=4 then 3-t v else 0)=
      (Finset.univ.filter (fun v => d v=3 ∧ t v=1)).card) :
    ∀ v,(d v=3 → t v=1) ∧ (d v=4 → t v=2) := by
  have hc4 : (Finset.univ.filter (fun v => d v=4)).card=4 := by
    have hv (v : Fin 8) : (if d v=3 then 1 else 0)+(if d v=4 then 1 else 0)=(1:ℕ) := by
      rcases hd v with h | h <;> simp [h]
    have hh := congrArg (fun f : Fin 8 → ℕ => ∑ v,f v) (funext hv)
    simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      smul_eq_mul,mul_one] at hh
    simp only [Finset.card_filter] at hk ⊢
    omega
  have hH : (Finset.univ.filter (fun v => d v=3 ∧ t v=1)).card≤4 := by
    rw [←hk]
    apply Finset.card_le_card
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hv).2.1⟩
  have hdef (v : Fin 8) : (if d v=4 then 1 else 0)≤(if d v=4 then 3-t v else 0) := by
    by_cases hv : d v=4
    · have hh := ht4 v hv
      simp only [hv,↓reduceIte]
      omega
    · simp [hv]
  have hsum : (∑ v, if d v=4 then 3-t v else 0)=4 := by
    have hh := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (Fin 8))) => hdef v)
    have hcard : (∑ v : Fin 8, if d v=4 then 1 else 0)=4 := by
      simpa only [Finset.card_filter] using hc4
    omega
  have hHfull : (Finset.univ.filter (fun v => d v=3 ∧ t v=1))=
      (Finset.univ.filter (fun v => d v=3)) := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hv).2.1⟩
    · omega
  have heq : ∀ v : Fin 8,(if d v=4 then 1 else 0)=(if d v=4 then 3-t v else 0) := by
    intro v
    apply (Finset.sum_eq_sum_iff_of_le (fun v (_ : v ∈ (Finset.univ : Finset (Fin 8))) => hdef v)).mp ?_ v (Finset.mem_univ _)
    simpa only [Finset.card_filter] using hc4.trans hsum.symm
  intro v
  constructor
  · intro hv
    have hm : v ∈ Finset.univ.filter (fun v => d v=3) := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
    rw [←hHfull] at hm
    exact (Finset.mem_filter.mp hm).2.2
  · intro hv
    have hh := heq v
    have ht := ht4 v hv
    simp only [hv,↓reduceIte] at hh
    omega

theorem cube_k4_types_fixed (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=4)
    (hnoE : ∀ v,Fintype.card (ContactNeighbor Y c v)=4 →
      faceCornerCount (boundaryArray Y c hY hc 3) v≠3) :
    ∀ v,(Fintype.card (ContactNeighbor Y c v)=3 → faceCornerCount (boundaryArray Y c hY hc 3) v=1) ∧
      (Fintype.card (ContactNeighbor Y c v)=4 → faceCornerCount (boundaryArray Y c hY hc 3) v=2) := by
  have ha := covering_no_rattlers Y c hY hc hcupper hirr hbound hne hsupport
  have hd (v : Fin 8) : Fintype.card (ContactNeighbor Y c v)=3 ∨ Fintype.card (ContactNeighbor Y c v)=4 := by
    have hh := degree_degree_four Y c hY hc.1 hcupper hirr hbound v (ha v)
    rw [←contactNeighbor_card_eq] at hh
    omega
  have ht := (rhombus_angles_assemble Y c hY hc hcupper hirr hbound hne hsupport).1
  apply four_four_triangle_types (fun v => Fintype.card (ContactNeighbor Y c v))
    (faceCornerCount (boundaryArray Y c hY hc 3)) hd hk (fun v => (ht v).1)
  · intro v hv
    have hh := (ht v).2 hv
    change faceCornerCount (boundaryArray Y c hY hc 3) v≤3 at hh
    have hn := hnoE v hv
    omega
  · exact auxiliary_graphs_incidence_identity Y c hY hc hcupper hirr hbound hne hsupport

#print axioms four_four_triangle_types
#print axioms cube_k4_types_fixed
end Blueprint.Thomson.Tail.Implementation
