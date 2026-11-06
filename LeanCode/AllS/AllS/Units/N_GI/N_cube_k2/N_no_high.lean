import AllS.Units.N_GI.N_auxiliary_graphs.N_incidence_identity

set_option maxHeartbeats 2000000
noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation
attribute [local instance] Classical.propDecidable

theorem diagonalGraph_high_neighbor_degree_three (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport) (v w : Fin 8)
    (hv : Fintype.card (ContactNeighbor Y c v)=3)
    (htv : faceCornerCount (boundaryArray Y c hY hc 3) v=1)
    (hvw : (diagonalGraph hsupport).Adj v w) : Fintype.card (ContactNeighbor Y c w)=3 := by
  have ha := covering_no_rattlers Y c hY hc hcupper hirr hbound hne hsupport
  have hd := degree_degree_four Y c hY hc.1 hcupper hirr hbound w (ha w)
  rw [←contactNeighbor_card_eq] at hd
  by_contra hnot
  have hw : Fintype.card (ContactNeighbor Y c w)=4 := by omega
  have ht : faceCornerCount (boundaryArray Y c hY hc 3) w≤3 :=
    ((rhombus_angles_assemble Y c hY hc hcupper hirr hbound hne hsupport).1 w).2 hw
  have hmix := diagonalGraph_no_mixed_types Y c hY hc hcupper hirr hbound hne hsupport w v
    ((diagonalGraph hsupport).adj_symm hvw)
  by_cases h3 : faceCornerCount (boundaryArray Y c hY hc 3) w=3
  · exact hmix.2.1 ⟨hw,h3,hv,htv⟩
  · exact hmix.2.2 ⟨hw,by omega,hv,htv⟩

theorem cube_k2_no_high (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : c ∈ Set.Ioo (0:ℝ) 1) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (hne : (packingContacts c Y).Nonempty)
    (hsupport : ∀ C : ContactBoundaryCycle Y c hY hc, C.StrictSupport)
    (hk : (degreeThreeVertices Y c).card=2) (v : Fin 8)
    (hv : Fintype.card (ContactNeighbor Y c v)=3) :
    faceCornerCount (boundaryArray Y c hY hc 3) v=0 := by
  have ht : faceCornerCount (boundaryArray Y c hY hc 3) v≤1 :=
    ((rhombus_angles_assemble Y c hY hc hcupper hirr hbound hne hsupport).1 v).1 hv
  by_contra hnot
  have ht1 : faceCornerCount (boundaryArray Y c hY hc 3) v=1 := by omega
  have hdiag := (diagonalGraph_typed_degrees Y c hY hc hcupper hirr hsupport v).2.2.1 hv ht1
  have hsubset : (diagonalGraph hsupport).neighborFinset v ⊆ (degreeThreeVertices Y c).erase v := by
    intro w hw
    have hadj := ((diagonalGraph hsupport).mem_neighborFinset v w).mp hw
    apply Finset.mem_erase.mpr
    refine ⟨((diagonalGraph hsupport).ne_of_adj hadj).symm,?_⟩
    have h3 := diagonalGraph_high_neighbor_degree_three Y c hY hc hcupper hirr hbound hne hsupport v w hv ht1 hadj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h3⟩
  have hle := Finset.card_le_card hsubset
  have hvset : v ∈ degreeThreeVertices Y c := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩
  rw [Finset.card_erase_of_mem hvset,hk] at hle
  change (diagonalGraph hsupport).degree v≤1 at hle
  omega

#print axioms diagonalGraph_high_neighbor_degree_three
#print axioms cube_k2_no_high
end Blueprint.Thomson.Tail.Implementation
