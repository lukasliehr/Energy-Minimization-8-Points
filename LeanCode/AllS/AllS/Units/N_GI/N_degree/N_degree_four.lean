import AllS.Units.N_GI.N_degree.N_contact_order
import AllS.Units.N_GI.N_constants.N_angle_cutoff

noncomputable section
open SquareAntiprismVerification
namespace Blueprint.Thomson.Tail.Implementation

theorem degree_degree_four (Y : Fin 8 → Point) (c : ℝ)
    (hY : IsConfiguration Y) (hc : 0<c) (hcupper : c<3/10)
    (hirr : PackingIrreducible c Y) (hbound : PackingInnerBound c Y)
    (i : Fin 8) (hne : ∃j, j≠i ∧ inner ℝ (Y i) (Y j)=c) :
    3≤(contactNeighborsWithin Y c Finset.univ i).card ∧
    (contactNeighborsWithin Y c Finset.univ i).card≤4 := by
  constructor
  · apply irreducible_degree_in_closed_set Y c hY.1 ⟨hc,by linarith⟩ hirr Finset.univ i
    · obtain ⟨j,hji,hij⟩ := hne
      exact ⟨j,hji.symm,hij⟩
    · intro j hj
      exact Finset.mem_univ j
  · obtain ⟨D,hlower,hupper,hsum⟩ := degree_contact_order Y c hY hc hcupper hirr hbound i hne
    rw [D.neighbor_card]
    exact angle_sum_at_most_four (D.size+1) (Real.arccos (c/(1+c)))
      (equilateral_angle_gt_two_pi_fifths c hc hcupper) D.gap hlower hsum

#print axioms degree_degree_four
end Blueprint.Thomson.Tail.Implementation
